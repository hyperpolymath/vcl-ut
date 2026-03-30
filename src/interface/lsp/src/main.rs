// SPDX-License-Identifier: PMPL-1.0-or-later
//! Language Server Protocol (LSP) implementation for VQL-UT
//!
//! This server provides LSP support for the VQL-UT query language.

use lsp_server::{Connection, Message, RequestId, Response};
use lsp_types::*;
use std::error::Error;

mod lib;
use lib::VqlutLsp;

/// Send an LSP result response, converting serialization failures to LSP
/// error responses rather than panicking. This ensures the server never
/// crashes on a malformed result — it reports the error to the client.
fn send_result<T: serde::Serialize>(
    connection: &Connection,
    id: RequestId,
    result: &T,
) -> Result<(), Box<dyn std::error::Error>> {
    match serde_json::to_value(result) {
        Ok(value) => {
            let resp = Response { id, result: Some(value), error: None };
            connection.sender.send(Message::Response(resp))?;
        }
        Err(e) => {
            let resp = Response {
                id,
                result: None,
                error: Some(lsp_server::ResponseError {
                    code: -32603, // Internal error (JSON-RPC)
                    message: format!("Result serialization failed: {}", e),
                    data: None,
                }),
            };
            connection.sender.send(Message::Response(resp))?;
        }
    }
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    // Create the transport (stdio, TCP, etc.)
    let (connection, io_threads) = Connection::stdio();

    // Initialize VQL-UT LSP
    let vqlut_lsp = VqlutLsp::new();

    // Run the server and wait for the two threads to end.
    let server_capabilities = serde_json::to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(
            TextDocumentSyncKind::Incremental,
        )),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(false),
            trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
            ..Default::default()
        }),
        definition_provider: Some(OneOf::Left(true)),
        ..Default::default()
    })?;

    let initialization_params = connection.initialize(server_capabilities).await?;
    let _initialized = initialization_params;

    // Main loop
    while let Some(msg) = connection.receiver.recv().await {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req).await? {
                    return Ok(());
                }
                match cast::<request::GotoDefinition>(req.clone()) {
                    Ok((id, params)) => {
                        let result = vqlut_lsp.handle_goto_definition(params);
                        send_result(&connection, id, &result)?;
                    }
                    _ => match cast::<request::HoverRequest>(req.clone()) {
                        Ok((id, params)) => {
                            let result = vqlut_lsp.handle_hover(params);
                            send_result(&connection, id, &result)?;
                        }
                        _ => match cast::<request::Completion>(req.clone()) {
                            Ok((id, params)) => {
                                let result = vqlut_lsp.handle_completion(params);
                                send_result(&connection, id, &result)?;
                            }
                            _ => {
                                eprintln!("Unknown request: {:?}", req);
                            }
                        },
                    },
                }
            }
            Message::Notification(not) => {
                if connection.handle_shutdown(&not).await? {
                    return Ok(());
                }
            }
            Message::Response(resp) => {
                eprintln!("Got response: {:?}", resp);
            }
        }
    }

    Ok(())
}

fn cast<U>(req: request::Request) -> Result<(RequestId, U::Params), request::Request>
where
    U: lsp_types::request::Request,
{
    req.extract(U::METHOD)
}
