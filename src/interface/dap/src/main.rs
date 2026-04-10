// SPDX-License-Identifier: PMPL-1.0-or-later
//! Debug Adapter Protocol (DAP) server for VCL-total
//!
//! This server provides DAP support for debugging VCL-total queries.

use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use vcltotal_dap::{dispatch_request, DapRequest};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:4715")?;
    println!("VCL-total DAP server listening on 127.0.0.1:4715");

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                std::thread::spawn(|| {
                    if let Err(e) = handle_client(stream) {
                        eprintln!("Error handling client: {}", e);
                    }
                });
            }
            Err(e) => {
                eprintln!("Error accepting connection: {}", e);
            }
        }
    }

    Ok(())
}

fn handle_client(stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let reader = BufReader::new(stream.try_clone()?);
    let mut writer = stream.try_clone()?;
    let mut seq_counter: i64 = 0;

    for line in reader.lines() {
        let line = line?;
        let request: DapRequest = serde_json::from_str(&line)?;
        let response = dispatch_request(&mut seq_counter, &request);
        let json = serde_json::to_string(&response)?;
        writeln!(writer, "{}", json)?;
    }

    Ok(())
}
