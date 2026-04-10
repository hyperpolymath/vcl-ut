// SPDX-License-Identifier: PMPL-1.0-or-later
//! Language Server Protocol (LSP) implementation for VCL-total
//!
//! This server provides LSP support for the VCL-total query language.
//! Uses lsp-server (synchronous) for the transport layer.

use lsp_server::{Connection, Message, RequestId, Response};
use lsp_types::*;
use std::error::Error;

use vcltotal_lsp::VqlutLsp;

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

fn cast<R>(req: lsp_server::Request) -> Result<(RequestId, R::Params), lsp_server::Request>
where
    R: lsp_types::request::Request,
{
    req.extract(R::METHOD).map_err(|e| match e {
        lsp_server::ExtractError::MethodMismatch(req) => req,
        lsp_server::ExtractError::JsonError { method: _, error: _ } => {
            // Deserialization failed — treat as unhandled (cannot recover the original request)
            panic!("JSON deserialization failed for LSP request")
        }
    })
}

fn main() -> Result<(), Box<dyn Error>> {
    // Create the transport (stdio)
    let (connection, io_threads) = Connection::stdio();

    // Initialize VCL-total LSP
    let vqlut_lsp = VqlutLsp::new();

    // Declare server capabilities
    let server_capabilities = serde_json::to_value(ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(
            TextDocumentSyncKind::FULL,
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

    let _initialization_params = connection.initialize(server_capabilities)?;

    // Main message loop (lsp-server is synchronous)
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                match cast::<request::GotoDefinition>(req.clone()) {
                    Ok((id, params)) => {
                        let result = vqlut_lsp.handle_goto_definition(params);
                        send_result(&connection, id, &result)?;
                    }
                    Err(req) => match cast::<request::HoverRequest>(req) {
                        Ok((id, params)) => {
                            let result = vqlut_lsp.handle_hover(params);
                            send_result(&connection, id, &result)?;
                        }
                        Err(req) => match cast::<request::Completion>(req) {
                            Ok((id, params)) => {
                                let result = vqlut_lsp.handle_completion(params);
                                send_result(&connection, id, &result)?;
                            }
                            Err(req) => {
                                eprintln!("Unhandled request: {:?}", req.method);
                            }
                        },
                    },
                }
            }
            Message::Notification(_not) => {
                // Notifications are fire-and-forget; no response needed.
            }
            Message::Response(resp) => {
                eprintln!("Unexpected response: {:?}", resp);
            }
        }
    }

    io_threads.join()?;
    Ok(())
}
