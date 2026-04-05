#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
//! VCL-total LSP Library
//!
//! This library provides LSP support for VCL-total.

use lsp_types::*;
use std::collections::HashMap;

pub struct VqlutLsp {
    pub schema: HashMap<String, Vec<String>>, // table_name -> columns
    /// Default VeriSimDB URL. Each project runs its own VeriSimDB instance on a
    /// unique port. Do NOT hardcode localhost:8080 — that is the VeriSimDB
    /// development server. Configure this per-workspace to match the target
    /// project's VeriSimDB port.
    pub verisimdb_url: String,
}

impl VqlutLsp {
    pub fn new() -> Self {
        Self {
            schema: HashMap::new(),
            // Empty by default — the user MUST configure this per-workspace.
            // Each project runs its own VeriSimDB instance on a different port.
            // Do NOT default to localhost:8080 (VeriSimDB dev server).
            verisimdb_url: String::new(),
        }
    }

    /// Connect to a specific VeriSimDB instance.
    ///
    /// Each workspace should call this with its own VeriSimDB URL before
    /// fetching schema. Do NOT pass "http://localhost:8080" — that port is
    /// reserved for the VeriSimDB development server itself.
    pub fn connect_verisimdb(&mut self, url: &str) {
        self.verisimdb_url = url.to_string();
    }

    pub fn fetch_schema(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // Guard: verisimdb_url must be configured per-workspace before use.
        if self.verisimdb_url.is_empty() {
            return Err("VeriSimDB URL not configured. Set verisimdb_url per-workspace \
                        (each project runs its own VeriSimDB instance on a unique port). \
                        Do NOT use localhost:8080 — that is the VeriSimDB dev server."
                .into());
        }

        // Connect to VeriSimDB via database-mcp cartridge
        // For now, simulate fetching schema from VeriSimDB
        // In production, this would use the database-mcp cartridge to execute a VCL query
        // and fetch the schema (tables and columns)

        // Simulate fetching schema from VeriSimDB
        self.schema.clear();
        self.schema.insert("users".to_string(), vec!["id".to_string(), "name".to_string(), "email".to_string()]);
        self.schema.insert("posts".to_string(), vec!["id".to_string(), "title".to_string(), "content".to_string()]);
        self.schema.insert("comments".to_string(), vec!["id".to_string(), "post_id".to_string(), "text".to_string()]);
        
        Ok(())
    }

    pub fn handle_goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Option<GotoDefinitionResponse> {
        // Extract the position and text from the params
        let position = params.text_document_position_params.position;
        let uri = params.text_document_position_params.text_document.uri;
        let line = position.line as usize;
        let character = position.character as usize;

        // TODO: Parse the VCL-total file at the given position to find the table/column
        // For now, return a dummy response with schema-based navigation
        if let Some((table, _)) = self.schema.iter().next() {
            Some(GotoDefinitionResponse::Scalar(Location {
                uri,
                range: Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + table.len() as u32,
                    },
                },
            }))
        } else {
            Some(GotoDefinitionResponse::Scalar(Location {
                uri,
                range: Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + 10,
                    },
                },
            }))
        }
    }

    pub fn handle_hover(&self, params: HoverParams) -> Option<Hover> {
        // Extract the position from the params
        let position = params.text_document_position_params.position;
        let line = position.line as usize;
        let character = position.character as usize;

        // TODO: Parse the VCL-total file at the given position to find the keyword/type
        // For now, return a dummy response
        Some(Hover {
            contents: HoverContents::Scalar(MarkedString::String(
                "VCL-total Keyword or Type".to_string(),
            )),
            range: Some(Range {
                start: Position {
                    line: line as u32,
                    character: character as u32,
                },
                end: Position {
                    line: line as u32,
                    character: character as u32 + 10,
                },
            }),
        })
    }

    pub fn handle_completion(&self, params: CompletionParams) -> Option<CompletionResponse> {
        // Extract the position from the params
        let position = params.text_document_position.position;
        let line = position.line as usize;
        let character = position.character as usize;

        // TODO: Parse the VCL-total file at the given position to suggest completions
        // For now, return a dummy response with some VCL-total keywords and schema
        let mut items = vec![
            CompletionItem {
                label: "SELECT".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total SELECT keyword".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "FROM".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total FROM keyword".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "WHERE".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total WHERE keyword".to_string()),
                ..Default::default()
            },
        ];

        // Add schema-based completions (tables and columns)
        for (table, columns) in &self.schema {
            items.push(CompletionItem {
                label: table.clone(),
                kind: Some(CompletionItemKind::STRUCT),
                detail: Some("VCL-total table".to_string()),
                ..Default::default()
            });
            for column in columns {
                items.push(CompletionItem {
                    label: format!("{}.{}", table, column),
                    kind: Some(CompletionItemKind::FIELD),
                    detail: Some("VCL-total column".to_string()),
                    ..Default::default()
                });
            }
        }

        Some(CompletionResponse::Array(items))
    }
}
