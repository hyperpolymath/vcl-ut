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
            return Err(
                "VeriSimDB URL not configured. Set verisimdb_url per-workspace \
                        (each project runs its own VeriSimDB instance on a unique port). \
                        Do NOT use localhost:8080 — that is the VeriSimDB dev server."
                    .into(),
            );
        }

        // Connect to VeriSimDB via database-mcp cartridge
        // For now, simulate fetching schema from VeriSimDB
        // In production, this would use the database-mcp cartridge to execute a VCL query
        // and fetch the schema (tables and columns)

        // Simulate fetching schema from VeriSimDB
        self.schema.clear();
        self.schema.insert(
            "users".to_string(),
            vec!["id".to_string(), "name".to_string(), "email".to_string()],
        );
        self.schema.insert(
            "posts".to_string(),
            vec!["id".to_string(), "title".to_string(), "content".to_string()],
        );
        self.schema.insert(
            "comments".to_string(),
            vec!["id".to_string(), "post_id".to_string(), "text".to_string()],
        );

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

    pub fn handle_completion(&self, _params: CompletionParams) -> Option<CompletionResponse> {
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
            CompletionItem {
                label: "GROUP BY".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total GROUP BY clause".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "ORDER BY".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total ORDER BY clause".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "HAVING".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total HAVING clause".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "LIMIT".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total LIMIT clause (Level 6: cardinality safety)".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "OFFSET".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total OFFSET clause".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "EFFECTS".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total EFFECTS clause (Level 7: effect tracking)".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "PROOF ATTACHED".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total PROOF clause (Level 4+: injection proof)".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "AT VERSION".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total version constraint (Level 8: temporal safety)".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "CONSUME AFTER".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total linearity annotation (Level 9: linear safety)".to_string()),
                ..Default::default()
            },
            CompletionItem {
                label: "USAGE LIMIT".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("VCL-total bounded usage (Level 9: linear safety)".to_string()),
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

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // VqlutLsp::new
    // -----------------------------------------------------------------------

    #[test]
    fn test_new_creates_empty_lsp() {
        let lsp = VqlutLsp::new();
        assert!(lsp.schema.is_empty());
        assert!(lsp.verisimdb_url.is_empty());
    }

    // -----------------------------------------------------------------------
    // connect_verisimdb
    // -----------------------------------------------------------------------

    #[test]
    fn test_connect_verisimdb_sets_url() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        assert_eq!(lsp.verisimdb_url, "http://localhost:9090");
    }

    #[test]
    fn test_connect_verisimdb_overwrites_previous_url() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.connect_verisimdb("http://localhost:7070");
        assert_eq!(lsp.verisimdb_url, "http://localhost:7070");
    }

    // -----------------------------------------------------------------------
    // fetch_schema
    // -----------------------------------------------------------------------

    #[test]
    fn test_fetch_schema_fails_without_url() {
        let mut lsp = VqlutLsp::new();
        let result = lsp.fetch_schema();
        assert!(result.is_err(), "fetch_schema must fail when URL is empty");
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("not configured"),
            "error should mention URL not configured, got: {err_msg}"
        );
    }

    #[test]
    fn test_fetch_schema_populates_tables() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.fetch_schema().expect("fetch_schema should succeed");

        assert_eq!(lsp.schema.len(), 3, "should have 3 tables");
        assert!(lsp.schema.contains_key("users"));
        assert!(lsp.schema.contains_key("posts"));
        assert!(lsp.schema.contains_key("comments"));
    }

    #[test]
    fn test_fetch_schema_populates_columns() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.fetch_schema().unwrap();

        let users_cols = lsp.schema.get("users").unwrap();
        assert!(users_cols.contains(&"id".to_string()));
        assert!(users_cols.contains(&"name".to_string()));
        assert!(users_cols.contains(&"email".to_string()));
    }

    #[test]
    fn test_fetch_schema_clears_previous() {
        let mut lsp = VqlutLsp::new();
        lsp.schema
            .insert("old_table".to_string(), vec!["col".to_string()]);
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.fetch_schema().unwrap();

        assert!(
            !lsp.schema.contains_key("old_table"),
            "old schema should be cleared"
        );
        assert_eq!(lsp.schema.len(), 3);
    }

    // -----------------------------------------------------------------------
    // handle_hover
    // -----------------------------------------------------------------------

    fn make_hover_params(line: u32, character: u32) -> HoverParams {
        HoverParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: Url::parse("file:///test.vcltotal").unwrap(),
                },
                position: Position { line, character },
            },
            work_done_progress_params: WorkDoneProgressParams {
                work_done_token: None,
            },
        }
    }

    #[test]
    fn test_handle_hover_returns_some() {
        let lsp = VqlutLsp::new();
        let result = lsp.handle_hover(make_hover_params(0, 0));
        assert!(result.is_some(), "hover should return a response");
    }

    #[test]
    fn test_handle_hover_contains_vcl_total_text() {
        let lsp = VqlutLsp::new();
        let hover = lsp.handle_hover(make_hover_params(0, 0)).unwrap();
        match &hover.contents {
            HoverContents::Scalar(MarkedString::String(s)) => {
                assert!(
                    s.contains("VCL-total"),
                    "hover text should mention VCL-total, got: {s}"
                );
            }
            other => panic!("unexpected hover contents: {other:?}"),
        }
    }

    #[test]
    fn test_handle_hover_range_matches_position() {
        let lsp = VqlutLsp::new();
        let hover = lsp.handle_hover(make_hover_params(5, 10)).unwrap();
        let range = hover.range.expect("hover should have a range");
        assert_eq!(range.start.line, 5);
        assert_eq!(range.start.character, 10);
    }

    // -----------------------------------------------------------------------
    // handle_goto_definition
    // -----------------------------------------------------------------------

    fn make_goto_params(line: u32, character: u32) -> GotoDefinitionParams {
        GotoDefinitionParams {
            text_document_position_params: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: Url::parse("file:///test.vcltotal").unwrap(),
                },
                position: Position { line, character },
            },
            work_done_progress_params: WorkDoneProgressParams {
                work_done_token: None,
            },
            partial_result_params: PartialResultParams {
                partial_result_token: None,
            },
        }
    }

    #[test]
    fn test_goto_definition_returns_some() {
        let lsp = VqlutLsp::new();
        let result = lsp.handle_goto_definition(make_goto_params(0, 0));
        assert!(result.is_some());
    }

    #[test]
    fn test_goto_definition_with_schema_uses_table_name() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.fetch_schema().unwrap();

        let result = lsp.handle_goto_definition(make_goto_params(2, 5));
        assert!(result.is_some());
        if let Some(GotoDefinitionResponse::Scalar(location)) = result {
            assert_eq!(location.range.start.line, 2);
            assert_eq!(location.range.start.character, 5);
        }
    }

    // -----------------------------------------------------------------------
    // handle_completion
    // -----------------------------------------------------------------------

    fn make_completion_params(line: u32, character: u32) -> CompletionParams {
        CompletionParams {
            text_document_position: TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: Url::parse("file:///test.vcltotal").unwrap(),
                },
                position: Position { line, character },
            },
            work_done_progress_params: WorkDoneProgressParams {
                work_done_token: None,
            },
            partial_result_params: PartialResultParams {
                partial_result_token: None,
            },
            context: None,
        }
    }

    #[test]
    fn test_completion_returns_keywords() {
        let lsp = VqlutLsp::new();
        let result = lsp.handle_completion(make_completion_params(0, 0));
        assert!(result.is_some());

        if let Some(CompletionResponse::Array(items)) = result {
            let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
            assert!(labels.contains(&"SELECT"));
            assert!(labels.contains(&"FROM"));
            assert!(labels.contains(&"WHERE"));
        } else {
            panic!("expected Array completion response");
        }
    }

    #[test]
    fn test_completion_includes_schema_tables_and_columns() {
        let mut lsp = VqlutLsp::new();
        lsp.connect_verisimdb("http://localhost:9090");
        lsp.fetch_schema().unwrap();

        let result = lsp.handle_completion(make_completion_params(0, 0));
        if let Some(CompletionResponse::Array(items)) = result {
            let labels: Vec<&str> = items.iter().map(|i| i.label.as_str()).collect();
            // Should include tables
            assert!(labels.contains(&"users"), "should include 'users' table");
            assert!(labels.contains(&"posts"), "should include 'posts' table");
            // Should include table.column combos
            assert!(
                labels.iter().any(|l| l.starts_with("users.")),
                "should include users.* columns"
            );
        } else {
            panic!("expected Array completion response");
        }
    }

    #[test]
    fn test_completion_without_schema_returns_only_keywords() {
        let lsp = VqlutLsp::new();
        let result = lsp.handle_completion(make_completion_params(0, 0));
        if let Some(CompletionResponse::Array(items)) = result {
            assert_eq!(
                items.len(),
                3,
                "without schema, only 3 keywords expected, got {}",
                items.len()
            );
        }
    }

    #[test]
    fn test_completion_keyword_items_have_correct_kind() {
        let lsp = VqlutLsp::new();
        let result = lsp.handle_completion(make_completion_params(0, 0));
        if let Some(CompletionResponse::Array(items)) = result {
            for item in &items {
                assert_eq!(
                    item.kind,
                    Some(CompletionItemKind::KEYWORD),
                    "keyword item '{}' should have KEYWORD kind",
                    item.label
                );
            }
        }
    }
}
