// SPDX-License-Identifier: PMPL-1.0-or-later
//! VQL-UT LSP Library
//!
//! This library provides LSP support for VQL-UT.

use lsp_types::*;
use std::collections::HashMap;

pub struct VqlutLsp {
    pub schema: HashMap<String, Vec<String>>, // table_name -> columns
    pub verisimdb_url: String,
}

impl VqlutLsp {
    pub fn new() -> Self {
        Self {
            schema: HashMap::new(),
            verisimdb_url: "http://localhost:8080".to_string(),
        }
    }

    pub fn connect_verisimdb(&mut self, url: &str) {
        self.verisimdb_url = url.to_string();
    }

    pub fn fetch_schema(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // Connect to VeriSimDB via database-mcp cartridge
        // For now, simulate fetching schema from VeriSimDB
        // In production, this would use the database-mcp cartridge to execute a VQL query
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

        // TODO: Parse the VQL-UT file at the given position to find the table/column
        // For now, return a dummy response with schema-based navigation
        if let Some((table, _)) = self.schema.iter().next() {
            Some(GotoDefinitionResponse::Scalar(GotoDefinitionLink {
                target_uri: uri,
                target_range: Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + table.len() as u32,
                    },
                },
                target_selection_range: Some(Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + table.len() as u32,
                    },
                }),
                origin_selection_range: None,
            }))
        } else {
            Some(GotoDefinitionResponse::Scalar(GotoDefinitionLink {
                target_uri: uri,
                target_range: Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + 10,
                    },
                },
                target_selection_range: Some(Range {
                    start: Position {
                        line: line as u32,
                        character: character as u32,
                    },
                    end: Position {
                        line: line as u32,
                        character: character as u32 + 10,
                    },
                }),
                origin_selection_range: None,
            }))
        }
    }

    pub fn handle_hover(&self, params: HoverParams) -> Option<Hover> {
        // Extract the position from the params
        let position = params.text_document_position_params.position;
        let line = position.line as usize;
        let character = position.character as usize;

        // TODO: Parse the VQL-UT file at the given position to find the keyword/type
        // For now, return a dummy response
        Some(Hover {
            contents: HoverContents::Scalar(MarkedString::String(
                "VQL-UT Keyword or Type".to_string(),
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
        let position = params.text_document_position_params.position;
        let line = position.line as usize;
        let character = position.character as usize;

        // TODO: Parse the VQL-UT file at the given position to suggest completions
        // For now, return a dummy response with some VQL-UT keywords and schema
        let mut items = vec![
            CompletionItem {
                label: "SELECT".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VQL-UT SELECT keyword".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "FROM".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VQL-UT FROM keyword".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "WHERE".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VQL-UT WHERE keyword".to_string()),
                ..Default::default()
            },
        ];

        // Add schema-based completions (tables and columns)
        for (table, columns) in &self.schema {
            items.push(CompletionItem {
                label: table.clone(),
                kind: Some(CompletionItemKind::STRUCT),
                detail: Some("VQL-UT table".to_string()),
                ..Default::default()
            });
            for column in columns {
                items.push(CompletionItem {
                    label: format!("{}.{}", table, column),
                    kind: Some(CompletionItemKind::FIELD),
                    detail: Some("VQL-UT column".to_string()),
                    ..Default::default()
                });
            }
        }

        Some(CompletionResponse {
            is_incomplete: false,
            items,
        })
    }
}
