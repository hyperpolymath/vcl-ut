// SPDX-License-Identifier: PMPL-1.0-or-later
//! Debug Adapter Protocol (DAP) implementation for VQL-UT
//!
//! This server provides DAP support for debugging VQL-UT queries.

use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};

#[derive(Debug, Serialize, Deserialize)]
struct DapRequest {
    seq: i64,
    r#type: String,
    command: String,
    arguments: Option<serde_json::Value>,
}

#[derive(Debug, Serialize)]
struct DapResponse {
    seq: i64,
    r#type: String,
    request_seq: i64,
    command: String,
    success: bool,
    message: Option<String>,
    body: Option<serde_json::Value>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:4715")?;
    println!("VQL-UT DAP server listening on 127.0.0.1:4715");

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

fn execute_vql_query(query: &str) -> String {
    // Connect to VeriSimDB via database-mcp cartridge
    // For now, simulate executing VQL queries and returning results
    // In production, this would use the database-mcp cartridge to execute the query
    // and return the results
    
    if query.to_lowercase().contains("select") {
        if query.to_lowercase().contains("users") {
            format!("Executing VQL query: {}\nResults: [\"id: 1, name: 'Alice', email: 'alice@example.com'\", \"id: 2, name: 'Bob', email: 'bob@example.com'\"]", query)
        } else if query.to_lowercase().contains("posts") {
            format!("Executing VQL query: {}\nResults: [\"id: 1, title: 'Hello World', content: 'First post'\", \"id: 2, title: 'VQL-UT', content: 'Query language'\"]", query)
        } else {
            format!("Executing VQL query: {}\nResults: []", query)
        }
    } else if query.to_lowercase().contains("insert") {
        format!("Executing VQL query: {}\nResults: Inserted 1 row", query)
    } else if query.to_lowercase().contains("update") {
        format!("Executing VQL query: {}\nResults: Updated 1 row", query)
    } else if query.to_lowercase().contains("delete") {
        format!("Executing VQL query: {}\nResults: Deleted 1 row", query)
    } else {
        format!("Executing VQL query: {}\nResults: []", query)
    }
}

fn handle_client(stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let reader = BufReader::new(stream.try_clone()?);
    let mut writer = stream.try_clone()?;

    for line in reader.lines() {
        let line = line?;
        let request: DapRequest = serde_json::from_str(&line)?;
        let response = match request.command.as_str() {
            "initialize" => {
                serde_json::to_string(&DapResponse {
                    seq: 1,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "initialize".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({
                        "supportsConfigurationDoneRequest": true,
                        "supportsFunctionBreakpoints": true,
                        "supportsConditionalBreakpoints": true,
                        "supportsEvaluateForHovers": true,
                        "exceptionBreakpointFilters": [],
                    })),
                })?
            }
            "launch" => {
                serde_json::to_string(&DapResponse {
                    seq: 2,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "launch".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"success": true})),
                })?
            }
            "setBreakpoints" => {
                serde_json::to_string(&DapResponse {
                    seq: 3,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "setBreakpoints".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"breakpoints": []})),
                })?
            }
            "threads" => {
                serde_json::to_string(&DapResponse {
                    seq: 4,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "threads".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"threads": [{"id": 1, "name": "main"}]}))
                })?
            }
            "stackTrace" => {
                serde_json::to_string(&DapResponse {
                    seq: 5,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "stackTrace".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"stackFrames": []})),
                })?
            }
            "scopes" => {
                serde_json::to_string(&DapResponse {
                    seq: 6,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "scopes".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"scopes": [{"name": "Locals", "variablesReference": 1, "expensive": false}]}))
                })?
            }
            "variables" => {
                serde_json::to_string(&DapResponse {
                    seq: 7,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "variables".to_string(),
                    success: true,
                    message: None,
                    body: Some(serde_json::json!({"variables": []})),
                })?
            }
            "continue" => {
                // TODO: Execute the query using database-mcp cartridge
                // For now, return a dummy response
                let query = if let Some(args) = &request.arguments {
                    args.get("query").and_then(|q| q.as_str()).unwrap_or("").to_string()
                } else {
                    "".to_string()
                };
                let result = execute_vql_query(&query);
                serde_json::to_string(&DapResponse {
                    seq: 9,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "continue".to_string(),
                    success: true,
                    message: Some(format!("Query executed: {}", result)),
                    body: None,
                })?
            }
            "disconnect" => {
                serde_json::to_string(&DapResponse {
                    seq: 8,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: "disconnect".to_string(),
                    success: true,
                    message: None,
                    body: None,
                })?
            }
            _ => {
                serde_json::to_string(&DapResponse {
                    seq: 0,
                    r#type: "response".to_string(),
                    request_seq: request.seq,
                    command: request.command,
                    success: false,
                    message: Some("Unknown command".to_string()),
                    body: None,
                })?
            }
        };

        writeln!(writer, "{}", response)?;
    }

    Ok(())
}
