#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
//! VCL-total DAP (Debug Adapter Protocol) Library
//!
//! Provides DAP message types and VCL query execution simulation
//! for the VCL-total debug adapter.

use serde::{Deserialize, Serialize};

/// A DAP request from the client (editor).
#[derive(Debug, Serialize, Deserialize)]
pub struct DapRequest {
    pub seq: i64,
    #[serde(rename = "type")]
    pub msg_type: String,
    pub command: String,
    pub arguments: Option<serde_json::Value>,
}

/// A DAP response to send back to the client.
#[derive(Debug, Serialize, Deserialize)]
pub struct DapResponse {
    pub seq: i64,
    #[serde(rename = "type")]
    pub msg_type: String,
    pub request_seq: i64,
    pub command: String,
    pub success: bool,
    pub message: Option<String>,
    pub body: Option<serde_json::Value>,
}

impl DapResponse {
    /// Build a successful response for the given request.
    pub fn success(seq: i64, request: &DapRequest, body: Option<serde_json::Value>) -> Self {
        Self {
            seq,
            msg_type: "response".to_string(),
            request_seq: request.seq,
            command: request.command.clone(),
            success: true,
            message: None,
            body,
        }
    }

    /// Build a failure response for an unknown command.
    pub fn unknown_command(request: &DapRequest) -> Self {
        Self {
            seq: 0,
            msg_type: "response".to_string(),
            request_seq: request.seq,
            command: request.command.clone(),
            success: false,
            message: Some("Unknown command".to_string()),
            body: None,
        }
    }
}

/// Simulate executing a VCL query and returning results.
///
/// In production this would use the database-mcp cartridge to execute
/// the query against VeriSimDB.
pub fn execute_vql_query(query: &str) -> String {
    if query.to_lowercase().contains("select") {
        if query.to_lowercase().contains("users") {
            format!(
                "Executing VCL query: {}\nResults: [\
                 \"id: 1, name: 'Alice', email: 'alice@example.com'\", \
                 \"id: 2, name: 'Bob', email: 'bob@example.com'\"]",
                query
            )
        } else if query.to_lowercase().contains("posts") {
            format!(
                "Executing VCL query: {}\nResults: [\
                 \"id: 1, title: 'Hello World', content: 'First post'\", \
                 \"id: 2, title: 'VCL-total', content: 'Query language'\"]",
                query
            )
        } else {
            format!("Executing VCL query: {}\nResults: []", query)
        }
    } else if query.to_lowercase().contains("insert") {
        format!("Executing VCL query: {}\nResults: Inserted 1 row", query)
    } else if query.to_lowercase().contains("update") {
        format!("Executing VCL query: {}\nResults: Updated 1 row", query)
    } else if query.to_lowercase().contains("delete") {
        format!("Executing VCL query: {}\nResults: Deleted 1 row", query)
    } else {
        format!("Executing VCL query: {}\nResults: []", query)
    }
}

/// Dispatch a DAP request to the appropriate handler and return the response.
pub fn dispatch_request(seq_counter: &mut i64, request: &DapRequest) -> DapResponse {
    *seq_counter += 1;
    let seq = *seq_counter;

    match request.command.as_str() {
        "initialize" => DapResponse::success(
            seq,
            request,
            Some(serde_json::json!({
                "supportsConfigurationDoneRequest": true,
                "supportsFunctionBreakpoints": true,
                "supportsConditionalBreakpoints": true,
                "supportsEvaluateForHovers": true,
                "exceptionBreakpointFilters": [],
            })),
        ),
        "launch" => DapResponse::success(seq, request, Some(serde_json::json!({"success": true}))),
        "setBreakpoints" => {
            DapResponse::success(seq, request, Some(serde_json::json!({"breakpoints": []})))
        }
        "threads" => DapResponse::success(
            seq,
            request,
            Some(serde_json::json!({"threads": [{"id": 1, "name": "main"}]})),
        ),
        "stackTrace" => {
            DapResponse::success(seq, request, Some(serde_json::json!({"stackFrames": []})))
        }
        "scopes" => DapResponse::success(
            seq,
            request,
            Some(
                serde_json::json!({"scopes": [{"name": "Locals", "variablesReference": 1, "expensive": false}]}),
            ),
        ),
        "variables" => {
            DapResponse::success(seq, request, Some(serde_json::json!({"variables": []})))
        }
        "continue" => {
            let query = request
                .arguments
                .as_ref()
                .and_then(|a| a.get("query"))
                .and_then(|q| q.as_str())
                .unwrap_or("");
            let result = execute_vql_query(query);
            let mut resp = DapResponse::success(seq, request, None);
            resp.message = Some(format!("Query executed: {}", result));
            resp
        }
        "disconnect" => DapResponse::success(seq, request, None),
        _ => DapResponse::unknown_command(request),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_request(command: &str, arguments: Option<serde_json::Value>) -> DapRequest {
        DapRequest {
            seq: 1,
            msg_type: "request".to_string(),
            command: command.to_string(),
            arguments,
        }
    }

    // -----------------------------------------------------------------------
    // execute_vql_query
    // -----------------------------------------------------------------------

    #[test]
    fn test_select_users_returns_results() {
        let result = execute_vql_query("SELECT * FROM users;");
        assert!(result.contains("Alice"));
        assert!(result.contains("Bob"));
    }

    #[test]
    fn test_select_posts_returns_results() {
        let result = execute_vql_query("SELECT * FROM posts;");
        assert!(result.contains("Hello World"));
        assert!(result.contains("VCL-total"));
    }

    #[test]
    fn test_select_unknown_table_returns_empty() {
        let result = execute_vql_query("SELECT * FROM widgets;");
        assert!(result.contains("Results: []"));
    }

    #[test]
    fn test_insert_returns_confirmation() {
        let result = execute_vql_query("INSERT INTO users VALUES (3, 'Carol');");
        assert!(result.contains("Inserted 1 row"));
    }

    #[test]
    fn test_update_returns_confirmation() {
        let result = execute_vql_query("UPDATE users SET name = 'Dave' WHERE id = 1;");
        assert!(result.contains("Updated 1 row"));
    }

    #[test]
    fn test_delete_returns_confirmation() {
        let result = execute_vql_query("DELETE FROM users WHERE id = 1;");
        assert!(result.contains("Deleted 1 row"));
    }

    #[test]
    fn test_unknown_query_returns_empty() {
        let result = execute_vql_query("EXPLAIN PLAN FOR x;");
        assert!(result.contains("Results: []"));
    }

    #[test]
    fn test_case_insensitive_matching() {
        let result = execute_vql_query("select * from users;");
        assert!(result.contains("Alice"), "should match case-insensitively");
    }

    // -----------------------------------------------------------------------
    // dispatch_request — command handling
    // -----------------------------------------------------------------------

    #[test]
    fn test_initialize_response() {
        let mut seq = 0;
        let req = make_request("initialize", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        assert_eq!(resp.command, "initialize");
        let body = resp.body.unwrap();
        assert_eq!(body["supportsConfigurationDoneRequest"], true);
    }

    #[test]
    fn test_launch_response() {
        let mut seq = 0;
        let req = make_request("launch", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        assert_eq!(resp.command, "launch");
    }

    #[test]
    fn test_set_breakpoints_response() {
        let mut seq = 0;
        let req = make_request("setBreakpoints", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        let body = resp.body.unwrap();
        assert!(body["breakpoints"].is_array());
    }

    #[test]
    fn test_threads_response() {
        let mut seq = 0;
        let req = make_request("threads", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        let body = resp.body.unwrap();
        let threads = body["threads"].as_array().unwrap();
        assert_eq!(threads.len(), 1);
        assert_eq!(threads[0]["name"], "main");
    }

    #[test]
    fn test_stack_trace_response() {
        let mut seq = 0;
        let req = make_request("stackTrace", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
    }

    #[test]
    fn test_scopes_response() {
        let mut seq = 0;
        let req = make_request("scopes", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        let body = resp.body.unwrap();
        let scopes = body["scopes"].as_array().unwrap();
        assert_eq!(scopes[0]["name"], "Locals");
    }

    #[test]
    fn test_variables_response() {
        let mut seq = 0;
        let req = make_request("variables", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
    }

    #[test]
    fn test_continue_executes_query() {
        let mut seq = 0;
        let req = make_request(
            "continue",
            Some(serde_json::json!({"query": "SELECT * FROM users;"})),
        );
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        let msg = resp.message.unwrap();
        assert!(msg.contains("Alice"), "continue should execute the query");
    }

    #[test]
    fn test_continue_without_query_arg() {
        let mut seq = 0;
        let req = make_request("continue", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
    }

    #[test]
    fn test_disconnect_response() {
        let mut seq = 0;
        let req = make_request("disconnect", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(resp.success);
        assert_eq!(resp.command, "disconnect");
    }

    #[test]
    fn test_unknown_command_fails() {
        let mut seq = 0;
        let req = make_request("nonExistentCommand", None);
        let resp = dispatch_request(&mut seq, &req);
        assert!(!resp.success);
        assert_eq!(resp.message.unwrap(), "Unknown command");
    }

    // -----------------------------------------------------------------------
    // DapResponse builders
    // -----------------------------------------------------------------------

    #[test]
    fn test_success_response_structure() {
        let req = make_request("test", None);
        let resp = DapResponse::success(42, &req, Some(serde_json::json!({"ok": true})));
        assert_eq!(resp.seq, 42);
        assert_eq!(resp.msg_type, "response");
        assert_eq!(resp.request_seq, 1);
        assert!(resp.success);
        assert!(resp.message.is_none());
    }

    #[test]
    fn test_unknown_command_response_structure() {
        let req = make_request("bad", None);
        let resp = DapResponse::unknown_command(&req);
        assert!(!resp.success);
        assert_eq!(resp.command, "bad");
    }

    // -----------------------------------------------------------------------
    // Serialization round-trip
    // -----------------------------------------------------------------------

    #[test]
    fn test_request_serialization_round_trip() {
        let req = make_request("initialize", Some(serde_json::json!({"clientID": "test"})));
        let json = serde_json::to_string(&req).unwrap();
        let parsed: DapRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.command, "initialize");
        assert_eq!(parsed.seq, 1);
    }

    #[test]
    fn test_response_serialization_round_trip() {
        let req = make_request("test", None);
        let resp = DapResponse::success(1, &req, Some(serde_json::json!({"data": 42})));
        let json = serde_json::to_string(&resp).unwrap();
        let parsed: DapResponse = serde_json::from_str(&json).unwrap();
        assert!(parsed.success);
        assert_eq!(parsed.body.unwrap()["data"], 42);
    }

    // -----------------------------------------------------------------------
    // Sequence counter
    // -----------------------------------------------------------------------

    #[test]
    fn test_seq_counter_increments() {
        let mut seq = 0;
        let req = make_request("initialize", None);
        let r1 = dispatch_request(&mut seq, &req);
        let r2 = dispatch_request(&mut seq, &req);
        let r3 = dispatch_request(&mut seq, &req);
        assert_eq!(r1.seq, 1);
        assert_eq!(r2.seq, 2);
        assert_eq!(r3.seq, 3);
    }
}
