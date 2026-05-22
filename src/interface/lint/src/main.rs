// SPDX-License-Identifier: MPL-2.0
//! VCL-total Linting Server
//!
//! This tool lints VCL-total query files for syntax and style issues.

use clap::Parser;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input file to lint
    #[arg(short, long)]
    input: PathBuf,
}

const MAX_FILE_BYTES: u64 = 50 * 1024 * 1024; // 50 MiB guard against unbounded reads

fn main() {
    let args = Args::parse();

    // Read the input file
    let input_path = args.input;
    let meta = fs::metadata(&input_path).expect("Unable to stat file");
    if meta.len() > MAX_FILE_BYTES {
        eprintln!("error: input file exceeds 50 MiB limit ({} bytes)", meta.len());
        std::process::exit(1);
    }
    let content = fs::read_to_string(&input_path).expect("Unable to read file");

    // Lint the content
    let issues = vcltotal_lint::lint_vqlut(&content);

    // Print the issues
    for issue in &issues {
        println!("{}:{}: {}", input_path.display(), issue.line, issue.message);
    }

    if issues.is_empty() {
        println!("No issues found");
    }
}
