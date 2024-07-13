use std::{
    collections::{BTreeMap, HashMap},
    convert::TryFrom,
    vec,
};

use anyhow::{anyhow, Context};
use cairovm_verifier_air::{
    public_memory::PublicInput as CairoPublicInput,
    trace::{
        config::Config as TraceConfig, Decommitment as TraceDecommitment,
        UnsentCommitment as TraceUnsentCommitment, Witness as TraceWitness,
    },
    types::{AddrValue, Page, SegmentInfo},
};
use cairovm_verifier_commitment::{
    table::{
        self,
        config::Config as TableCommitmentConfig,
        types::{Decommitment as TableDecommitment, Witness as TableWitness},
    },
    vector::{config::Config as VectorCommitmentConfig, types::Witness as VectorWitness},
};
use cairovm_verifier_fri::{
    config::Config as FriConfig,
    types::{LayerWitness, UnsentCommitment as FriUnsentCommitment, Witness as FriWitness},
};
use cairovm_verifier_pow::{
    config::Config as ProofOfWorkConfig, pow::UnsentCommitment as ProofOfWorkUnsentCommitment,
};
use cairovm_verifier_stark::{
    config::StarkConfig,
    types::{StarkProof, StarkUnsentCommitment, StarkWitness},
};
use num_bigint::BigUint;
use serde::Deserialize;
use serde_felt::from_felts_with_lengths;
use starknet_crypto::FieldElement;
use starknet_types_core::felt::Felt;

use crate::{
    annotations::Annotations,
    builtins::Builtin,
    layout::Layout,
    proof_params::{ProofParameters, ProverConfig},
    proof_structure::ProofStructure,
    utils::log2_if_power_of_2,
};

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct ProofJSON {
    proof_parameters: ProofParameters,
    #[serde(default)]
    annotations: Vec<String>,
    public_input: PublicInput,
    proof_hex: String,
    prover_config: ProverConfig,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct MemorySegmentAddress {
    begin_addr: u32,
    stop_ptr: u32,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct PublicMemoryElement {
    address: u32,
    page: u32,
    value: String,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct PublicInput {
    dynamic_params: Option<BTreeMap<String, BigUint>>,
    pub layout: Layout,
    memory_segments: HashMap<String, MemorySegmentAddress>,
    pub n_steps: u32,
    public_memory: Vec<PublicMemoryElement>,
    rc_min: u32,
    rc_max: u32,
}

pub fn bigint_to_fe(bigint: &BigUint) -> Felt {
    Felt::from_hex(&bigint.to_str_radix(16)).unwrap()
}

pub fn bigints_to_fe(bigint: &[BigUint]) -> Vec<Felt> {
    bigint.iter().map(bigint_to_fe).collect()
}

impl ProofJSON {
    const COMPONENT_HEIGHT: u32 = 16;
    pub fn stark_config(&self) -> anyhow::Result<StarkConfig> {
        let stark = &self.proof_parameters.stark;
        let n_verifier_friendly_commitment_layers =
            self.proof_parameters.n_verifier_friendly_commitment_layers;

        let consts = match self
            .public_input
            .layout
            .get_dynamics_or_consts(&self.public_input.dynamic_params)
        {
            Some(c) => c,
            None => anyhow::bail!(
                "There were some constant overrides in the dynamic params but couldn't be parsed!"
            ),
        };

        let log_eval_domain_size = self.log_eval_damain_size()?;
        let traces = TraceConfig {
            original: TableCommitmentConfig {
                n_columns: consts.num_columns_first.into(),
                vector: VectorCommitmentConfig {
                    height: log_eval_domain_size.into(),
                    n_verifier_friendly_commitment_layers: n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
            interaction: TableCommitmentConfig {
                n_columns: consts.num_columns_second.into(),
                vector: VectorCommitmentConfig {
                    height: log_eval_domain_size.into(),
                    n_verifier_friendly_commitment_layers: n_verifier_friendly_commitment_layers
                        .into(),
                },
            },
        };

        let composition = TableCommitmentConfig {
            n_columns: consts.constraint_degree.into(),
            vector: VectorCommitmentConfig {
                height: log_eval_domain_size.into(),
                n_verifier_friendly_commitment_layers: n_verifier_friendly_commitment_layers.into(),
            },
        };

        let fri = self.proof_parameters.stark.fri.clone();

        let proof_of_work = ProofOfWorkConfig {
            n_bits: fri.proof_of_work_bits as u8,
        };
        let n_queries = fri.n_queries;

        let layer_log_sizes = self.layer_log_sizes()?;

        let fri_step_list = fri.fri_step_list;
        let log_last_layer_degree_bound = log2_if_power_of_2(fri.last_layer_degree_bound)
            .ok_or(anyhow::anyhow!("Invalid last layer degree bound"))?;
        let fri = FriConfig {
            log_input_size: layer_log_sizes[0].into(),
            n_layers: fri_step_list.len().into(),
            inner_layers: fri_step_list[1..]
                .iter()
                .zip(layer_log_sizes[2..].iter())
                .map(|(layer_steps, layer_log_rows)| TableCommitmentConfig {
                    n_columns: 2_u32.pow(*layer_steps).into(),
                    vector: VectorCommitmentConfig {
                        height: layer_log_rows.to_owned().into(),
                        n_verifier_friendly_commitment_layers:
                            n_verifier_friendly_commitment_layers.into(),
                    },
                })
                .collect(),
            fri_step_sizes: fri_step_list.into_iter().map(|a| a.into()).collect(),
            log_last_layer_degree_bound: log_last_layer_degree_bound.into(),
        };

        Ok(StarkConfig {
            traces,
            composition,
            fri,
            proof_of_work,
            log_trace_domain_size: self.log_trace_domain_size()?.into(),
            n_queries: n_queries.into(),
            log_n_cosets: stark.log_n_cosets.into(),
            n_verifier_friendly_commitment_layers: n_verifier_friendly_commitment_layers.into(),
        })
    }

    fn log_trace_domain_size(&self) -> anyhow::Result<u32> {
        let consts = self.public_input.layout.get_consts();
        let effective_component_height = Self::COMPONENT_HEIGHT * consts.cpu_component_step;
        log2_if_power_of_2(effective_component_height * self.public_input.n_steps)
            .ok_or(anyhow::anyhow!("Invalid cpu component step"))
    }

    fn log_eval_damain_size(&self) -> anyhow::Result<u32> {
        Ok(self.log_trace_domain_size()? + self.proof_parameters.stark.log_n_cosets)
    }

    fn layer_log_sizes(&self) -> anyhow::Result<Vec<u32>> {
        let mut layer_log_sizes = vec![self.log_eval_damain_size()?];
        for layer_step in &self.proof_parameters.stark.fri.fri_step_list {
            layer_log_sizes.push(layer_log_sizes.last().unwrap() - layer_step);
        }
        Ok(layer_log_sizes)
    }

    pub fn public_input(
        public_input: PublicInput,
        // z: BigUint,
        // alpha: BigUint,
    ) -> anyhow::Result<CairoPublicInput> {
        let continuous_page_headers = vec![];
        // Self::continuous_page_headers(&public_input.public_memory, z, alpha)?; this line does for now anyway
        let main_page = Self::main_page(&public_input.public_memory)?;
        let dynamic_params = public_input
            .dynamic_params
            .unwrap_or_default()
            .into_iter()
            .map(|e| Felt::from_hex(&e.1.to_str_radix(16)).context("Invalid dynamic param"))
            .collect::<anyhow::Result<Vec<Felt>>>()?;
        let memory_segments = Builtin::sort_segments(public_input.memory_segments)
            .into_iter()
            .map(|s| SegmentInfo {
                begin_addr: s.begin_addr.into(),
                stop_ptr: s.stop_ptr.into(),
            })
            .collect::<Vec<_>>();
        let layout = Felt::from_hex(&prefix_hex::encode(public_input.layout.bytes_encode()))?;
        let (padding_addr, padding_value) = match public_input.public_memory.first() {
            Some(m) => (m.address, Felt::from_hex(&m.value)?),
            None => anyhow::bail!("Invalid public memory"),
        };
        Ok(CairoPublicInput {
            log_n_steps: log2_if_power_of_2(public_input.n_steps)
                .ok_or(anyhow::anyhow!("Invalid number of steps"))?
                .into(),
            range_check_min: public_input.rc_min.into(),
            range_check_max: public_input.rc_max.into(),
            layout,
            dynamic_params,
            segments: memory_segments,
            padding_addr: padding_addr.into(),
            padding_value,
            main_page,
            continuous_page_headers,
        })
    }

    fn main_page(public_memory: &[PublicMemoryElement]) -> anyhow::Result<Page> {
        let vec_add_value = public_memory
            .iter()
            .filter(|m| m.page == 0)
            .map(|m| {
                Ok(AddrValue {
                    address: m.address.into(),
                    value: Felt::from_hex(&m.value).context("Invalid memory value")?,
                })
            })
            .collect::<anyhow::Result<Vec<AddrValue>>>()?;
        Ok(Page(vec_add_value))
    }

    fn _continuous_page_headers(
        _public_memory: &[PublicMemoryElement],
        _z: BigUint,
        _alpha: BigUint,
    ) -> anyhow::Result<Vec<BigUint>> {
        //TODO: Do it properly
        Ok(vec![])
    }

    fn stark_unsent_commitment(&self, annotations: &Annotations) -> StarkUnsentCommitment {
        StarkUnsentCommitment {
            traces: TraceUnsentCommitment {
                original: bigint_to_fe(&annotations.original_commitment_hash),
                interaction: bigint_to_fe(&annotations.interaction_commitment_hash),
            },
            composition: bigint_to_fe(&annotations.composition_commitment_hash),
            oods_values: bigints_to_fe(&annotations.oods_values),
            fri: FriUnsentCommitment {
                inner_layers: bigints_to_fe(&annotations.fri_layers_commitments),
                last_layer_coefficients: bigints_to_fe(&annotations.fri_last_layer_coefficients),
            },
            proof_of_work: ProofOfWorkUnsentCommitment {
                nonce: annotations.proof_of_work_nonce.to_u64_digits()[0],
            },
        }
    }

    fn stark_witness(annotations: &Annotations) -> StarkWitness {
        StarkWitness {
            traces_decommitment: TraceDecommitment {
                original: TableDecommitment {
                    values: bigints_to_fe(&annotations.original_leaves),
                },
                interaction: TableDecommitment {
                    values: bigints_to_fe(&annotations.interaction_leaves),
                },
            },
            traces_witness: TraceWitness {
                original: TableWitness {
                    vector: VectorWitness {
                        authentications: bigints_to_fe(&annotations.original_authentications),
                    },
                },
                interaction: TableWitness {
                    vector: VectorWitness {
                        authentications: bigints_to_fe(&annotations.interaction_authentications),
                    },
                },
            },
            composition_decommitment: table::types::Decommitment {
                values: bigints_to_fe(&annotations.composition_leaves),
            },
            composition_witness: TableWitness {
                vector: VectorWitness {
                    authentications: bigints_to_fe(&annotations.composition_authentications),
                },
            },
            fri_witness: FriWitness {
                layers: annotations
                    .fri_witnesses
                    .iter()
                    .map(|w| LayerWitness {
                        leaves: bigints_to_fe(&w.leaves),
                        table_witness: TableWitness {
                            vector: VectorWitness {
                                authentications: bigints_to_fe(&w.authentications),
                            },
                        },
                    })
                    .collect(),
            },
        }
    }
}

#[derive(Debug)]
struct HexProof(Vec<FieldElement>);

impl TryFrom<&str> for HexProof {
    type Error = anyhow::Error;
    fn try_from(value: &str) -> anyhow::Result<Self> {
        let hex: Vec<u8> = prefix_hex::decode(value).map_err(|_| anyhow!("Invalid hex"))?;
        let mut result = vec![];
        for chunk in hex.chunks(32) {
            result.push(FieldElement::from_byte_slice_be(chunk)?);
        }

        Ok(HexProof(result))
    }
}

pub fn proof_from_annotations(value: ProofJSON) -> anyhow::Result<StarkProof> {
    let config = value.stark_config()?;

    let annotations = Annotations::new(
        &value
            .annotations
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        value.proof_parameters.stark.fri.fri_step_list.len(),
    )?;

    let public_input = ProofJSON::public_input(value.public_input.clone())?;

    let unsent_commitment = value.stark_unsent_commitment(&annotations);
    let witness = ProofJSON::stark_witness(&annotations);

    Ok(StarkProof {
        config,
        public_input,
        unsent_commitment,
        witness,
    })
}

impl TryFrom<ProofJSON> for StarkProof {
    type Error = anyhow::Error;
    fn try_from(value: ProofJSON) -> anyhow::Result<Self> {
        let config = value.stark_config()?;

        let public_input = ProofJSON::public_input(
            value.public_input.clone(),
            // annotations.z.clone(),
            // annotations.alpha.clone(),
        )?;

        let hex = HexProof::try_from(value.proof_hex.as_str())?;

        let proof_structure = ProofStructure::new(
            &value.proof_parameters,
            &value.prover_config,
            value.public_input.layout,
            Some(hex.0.len()),
        );

        assert_eq!(hex.0.len(), proof_structure.expected_len());

        let (unsent_commitment, witness): (StarkUnsentCommitment, StarkWitness) =
            from_felts_with_lengths(
                &hex.0,
                vec![
                    ("oods_values", vec![proof_structure.oods]),
                    ("inner_layers", vec![proof_structure.layer_count]),
                    (
                        "last_layer_coefficients",
                        vec![proof_structure.last_layer_degree_bound],
                    ),
                    // WITNESS
                    ("original_leaves", vec![proof_structure.first_layer_queries]),
                    (
                        "original_authentications",
                        vec![proof_structure.authentications],
                    ),
                    (
                        "interaction_leaves",
                        vec![proof_structure.composition_decommitment],
                    ),
                    (
                        "interaction_authentications",
                        vec![proof_structure.authentications],
                    ),
                    (
                        "composition_leaves",
                        vec![proof_structure.composition_leaves],
                    ),
                    (
                        "composition_authentications",
                        vec![proof_structure.authentications],
                    ),
                    ("fri_witness", vec![proof_structure.witness.len()]),
                    ("leaves", proof_structure.layer),
                    ("table_witness", proof_structure.witness),
                ]
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
            )?;

        let proof = StarkProof {
            config,
            public_input,
            unsent_commitment,
            witness,
        };

        Ok(proof)
    }
}
