use std::convert::TryFrom;

mod annotations;
mod builtins;
pub mod json_parser;
mod layout;
mod proof_params;
mod proof_structure;
mod utils;

pub use crate::json_parser::ProofJSON;
use cairovm_verifier_stark::types::StarkProof;
pub use serde_felt::to_felts;

pub fn parse(input: &str) -> anyhow::Result<StarkProof> {
    let proof_json = serde_json::from_str::<ProofJSON>(input)?;
    let stark_proof = StarkProof::try_from(proof_json)?;

    Ok(stark_proof)
}

pub fn parse_raw(input: &str) -> anyhow::Result<StarkProof> {
    let proof_json = serde_json::from_str::<ProofJSON>(input)?;
    let stark_proof = StarkProof::try_from(proof_json)?;
    Ok(stark_proof)
}
