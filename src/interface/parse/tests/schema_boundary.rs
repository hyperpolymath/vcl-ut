// SPDX-License-Identifier: MPL-2.0
// v1 gate JSON schema regression tests, exercising the binary boundary.
use std::io::Write;
use std::process::{Command, Stdio};
use serde_json::{json, Value};

const GATE: &str = env!("CARGO_BIN_EXE_vclt-gate");
fn run(request: Value) -> (i32, Value) {
    let mut child = Command::new(GATE).stdin(Stdio::piped()).stdout(Stdio::piped())
        .spawn().expect("spawn vclt-gate");
    child.stdin.take().expect("stdin").write_all(request.to_string().as_bytes())
        .expect("send request");
    let output = child.wait_with_output().expect("output");
    (output.status.code().expect("status"),
     serde_json::from_slice(&output.stdout).expect("response JSON"))
}
fn request(field: Value) -> Value {
    json!({"schema_version":1,
           "statement":"INSPECT GRAPH.name FROM OCTAD 'x' WHERE GRAPH.name = $name",
           "schema":{"graph":{"fields":[field]}}})
}
#[test]
fn absent_nullable_is_conservatively_nullable() {
    let (code, response) = run(request(json!({"name":"name","ty":"TString"})));
    assert_eq!(code, 1);
    assert_eq!(response["certified_level"], -1);
    assert_eq!(response["levels"][2]["level"], 3);
    assert_eq!(response["levels"][2]["status"], "fail");
}
#[test]
fn explicit_non_nullable_preserves_admission() {
    let (code, response) = run(request(json!({
        "name":"name","ty":"TString","nullable":false,"indexed":false
    })));
    assert_eq!(code, 0);
    assert_eq!(response["certified_level"], 4);
}
#[test]
fn malformed_schema_metadata_rejects_as_gate_error() {
    for field in [
        json!({"name":"name","ty":"TString","nullable":"false"}),
        json!({"name":"name","ty":"TString","nullable":null}),
        json!({"name":"name","ty":"TString","nullable":0}),
        json!({"name":"name","ty":"TString","nullable":false,"indexed":"true"})
    ] {
        let (code, response) = run(request(field));
        assert_eq!(code, 2);
        assert_eq!(response["error"]["kind"], "bad_schema");
    }
}
#[test]
fn malformed_schema_shapes_reject_as_gate_error() {
    for schema in [
        json!(null), json!([]), json!({"graph":null}),
        json!({"graph":{"fields":null}}),json!({"graph":{"fields":{}}}),
        json!({"graph":{"fields":"missing"}})
    ] {
        let mut req = request(json!({"name":"name","ty":"TString","nullable":false}));
        req["schema"] = schema;
        let (code, response) = run(req);
        assert_eq!(code, 2);
        assert_eq!(response["error"]["kind"], "bad_schema");
    }
}
#[test]
fn absent_slot_still_normalizes_to_empty_fixed_slot() {
    let (code, response) = run(json!({
        "schema_version":1,
        "statement":"INSPECT GRAPH FROM OCTAD 'x' LIMIT 1","schema":{}
    }));
    assert_eq!(code, 0);
    assert_eq!(response["admissible"], true);
}
