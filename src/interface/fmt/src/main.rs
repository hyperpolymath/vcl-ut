// SPDX-License-Identifier: MPL-2.0
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

const MAX_FILE_BYTES: u64 = 50 * 1024 * 1024; // 50 MiB guard against unbounded reads

fn main() -> std::io::Result<()> {
    let args = Args::parse();

    // Read the input file
    let input_path = args.input;
    let meta = fs::metadata(&input_path)
        .map_err(|e| std::io::Error::new(e.kind(), format!("{}: {e}", input_path.display())))?;
    if meta.len() > MAX_FILE_BYTES {
        eprintln!("error: input file exceeds 50 MiB limit ({} bytes)", meta.len());
        std::process::exit(1);
    }
    let content = fs::read_to_string(&input_path)
        .map_err(|e| std::io::Error::new(e.kind(), format!("{}: {e}", input_path.display())))?;

    // Format the content (basic indentation for now)
    let formatted = vcltotal_fmt::format_vqlut(&content);

    // Write the output file
    let output_path = args.output.unwrap_or(input_path);
    fs::write(&output_path, formatted)
        .map_err(|e| std::io::Error::new(e.kind(), format!("{}: {e}", output_path.display())))?;

    println!("Formatted {}", output_path.display());

    Ok(())
}
