// SPDX-License-Identifier: MPL-2.0
//! Language Server Protocol (LSP) implementation for VCL-total
//!
//! This server provides LSP support for the VCL-total query language.
//! Uses lsp-server (synchronous) for the transport layer.

// Binary-side mirror of the `vclt-gate` posture: the server must report
// failures to the client, never crash on them.

#![forbid(unsafe_code)]

#![deny(clippy::unwrap_used, clippy::expect_used)]

use lsp_server::{Connection, Message, RequestId, Response};
use lsp_types::*;
use std::error::Error;

use vcltotal_lsp::VqlutLsp;

/// Send an LSP error response. Failures the server can attribute to a
/// request (malformed params, unserializable results) are *reported* to
/// the client — the server never crashes on them.
fn send_error(
    connection: &Connection,
    id: RequestId,
    code: i32,
    message: String,
) -> Result<(), Box<dyn std::error::Error>> {
    let resp = Response {
        id,
        result: None,
        error: Some(lsp_server::ResponseError { code, message, data: None }),
    };
    connection.sender.send(Message::Response(resp))?;
    Ok(())
}

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
            // Internal error (JSON-RPC)
            send_error(connection, id, -32603, format!("Result serialization failed: {e}"))?;
        }
    }
    Ok(())
}

/// Outcome of attempting to read an LSP request as a typed request
/// (see `cast`); `P` is the expected params type.
enum Cast<P> {
    /// Method matched and params deserialized: ready to handle.
    Hit(RequestId, P),
    /// Method matched but params failed JSON deserialization. Carries
    /// the id rescued before `extract` consumed the request, so the
    /// server answers `Invalid params` instead of crashing — malformed
    /// input fails closed, never panics.
    BadParams { id: RequestId, method: String, error: String },
    /// Method did not match: the untouched request, for the next cast
    /// attempt in the dispatch chain.
    Mismatch(lsp_server::Request),
}

fn cast<R>(req: lsp_server::Request) -> Cast<R::Params>
where
    R: lsp_types::request::Request,
{
    // `extract` consumes the request and drops the id on a params
    // deserialization failure — so rescue it first. A malformed request
    // is then answerable (JSON-RPC `Invalid params`, -32602) instead of
    // a server crash.
    let id = req.id.clone();
    match req.extract(R::METHOD) {
        Ok((id, params)) => Cast::Hit(id, params),
        Err(lsp_server::ExtractError::MethodMismatch(req)) => Cast::Mismatch(req),
        Err(lsp_server::ExtractError::JsonError { method, error }) => Cast::BadParams {
            id,
            method,
            error: error.to_string(),
        },
    }
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
                match cast::<request::GotoDefinition>(req) {
                    Cast::Hit(id, params) => {
                        let result = vqlut_lsp.handle_goto_definition(params);
                        send_result(&connection, id, &result)?;
                    }
                    Cast::BadParams { id, method, error } => {
                        // Invalid params (JSON-RPC)
                        send_error(
                            &connection,
                            id,
                            -32602,
                            format!("Invalid params for {method}: {error}"),
                        )?;
                    }
                    Cast::Mismatch(req) => match cast::<request::HoverRequest>(req) {
                        Cast::Hit(id, params) => {
                            let result = vqlut_lsp.handle_hover(params);
                            send_result(&connection, id, &result)?;
                        }
                        Cast::BadParams { id, method, error } => {
                            send_error(
                                &connection,
                                id,
                                -32602,
                                format!("Invalid params for {method}: {error}"),
                            )?;
                        }
                        Cast::Mismatch(req) => match cast::<request::Completion>(req) {
                            Cast::Hit(id, params) => {
                                let result = vqlut_lsp.handle_completion(params);
                                send_result(&connection, id, &result)?;
                            }
                            Cast::BadParams { id, method, error } => {
                                send_error(
                                    &connection,
                                    id,
                                    -32602,
                                    format!("Invalid params for {method}: {error}"),
                                )?;
                            }
                            Cast::Mismatch(req) => {
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
