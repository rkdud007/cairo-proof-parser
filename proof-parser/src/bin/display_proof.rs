use std::{
    fs,
    io::{self, Read},
};

use cairo_proof_parser::{parse, to_felts};

fn main() -> anyhow::Result<()> {
    let file_path = "cairo0_example_proof.json";
    let file = fs::read_to_string(file_path)?;

    // Parse the input as an AST
    let proof = parse(&file)?;
    let serialized = to_felts(&proof);

    println!("{serialized:?}");
    Ok(())
}
