// SPDX-License-Identifier: PMPL-1.0-or-later
//! VCL-total Formatting Server
//!
//! This tool formats VCL-total query files.

use clap::Parser;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input file to format
    #[arg(short, long)]
    input: PathBuf,

    /// Output file (default: overwrite input)
    #[arg(short, long)]
    output: Option<PathBuf>,
}

fn main() {
    let args = Args::parse();

    // Read the input file
    let input_path = args.input;
    let content = fs::read_to_string(&input_path).expect("Unable to read file");

    // Format the content (basic indentation for now)
    let formatted = vqlut_fmt::format_vqlut(&content);

    // Write the output file
    let output_path = args.output.unwrap_or(input_path);
    fs::write(&output_path, formatted).expect("Unable to write file");

    println!("Formatted {}", output_path.display());
}
