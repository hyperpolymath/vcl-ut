// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! vclt-gate transport tests (contract §"Transport").
//!
//! These run the built binary, unlike `gate.rs`: the transport is the
//! process boundary itself. stdin and `--input <path>` must be the same
//! function of the request, and any other invocation is a gate error.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const GATE: &str = env!("CARGO_BIN_EXE_vclt-gate");

fn via_stdin(request: &str) -> Output {
    let mut child = Command::new(GATE)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(request.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn gate(args: &[&std::ffi::OsStr]) -> Output {
    Command::new(GATE)
        .args(args)
        .stdin(Stdio::null())
        .output()
        .unwrap()
}

/// A request file in a fresh directory whose name carries shell
/// metacharacters, so a consumer that quoted the path wrongly would fail.
fn request_file(test: &str, request: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "vclt-gate {test} '$(x)' ;|& {}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("request.json");
    std::fs::write(&path, request).unwrap();
    path
}

fn error_kind(out: &Output) -> String {
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    v["error"]["kind"].as_str().unwrap().to_string()
}

const ADMITTED: &str =
    r#"{"schema_version":1,"statement":"INSPECT GRAPH FROM HEXAD 'abc' LIMIT 1","schema":{}}"#;

#[test]
fn input_file_and_stdin_give_the_same_verdict() {
    // Admitted, rejected and gate-error requests: same stdout, same exit.
    let rejected = r#"{"schema_version":1,"statement":"INSPECT GRAPH FROM HEXAD abc WHERE id = '1' OR '1'='1'","schema":{}}"#;
    let bad_version =
        r#"{"schema_version":7,"statement":"INSPECT GRAPH FROM HEXAD 'abc'","schema":{}}"#;
    for (i, request) in [ADMITTED, rejected, bad_version].into_iter().enumerate() {
        let path = request_file(&format!("same-{i}"), request);
        let from_file = gate(&["--input".as_ref(), path.as_os_str()]);
        let from_stdin = via_stdin(request);
        assert_eq!(
            from_file.status.code(),
            from_stdin.status.code(),
            "{request}"
        );
        assert_eq!(from_file.stdout, from_stdin.stdout, "{request}");
    }
    assert_eq!(via_stdin(ADMITTED).status.code(), Some(0));
}

#[test]
fn hostile_statement_in_input_file_arrives_verbatim() {
    // The request file is data: metacharacters in it are never interpreted.
    let request = r#"{"schema_version":1,"statement":"INSPECT GRAPH FROM HEXAD abc WHERE id = '1' ; rm -rf / | x & `id` $(whoami) > /tmp/pwn","schema":{"probe":"' ; | & ` $( ) > \n tab\there"}}"#;
    let path = request_file("hostile", request);
    let from_file = gate(&["--input".as_ref(), path.as_os_str()]);
    assert_eq!(from_file.stdout, via_stdin(request).stdout);
}

#[test]
fn missing_input_file_is_a_gate_error() {
    let out = gate(&[
        "--input".as_ref(),
        "/nonexistent/vclt-gate/request.json".as_ref(),
    ]);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(error_kind(&out), "io_error");
}

#[test]
fn any_other_invocation_is_a_gate_error() {
    let path = request_file("argv", ADMITTED);
    for args in [
        vec!["--input".as_ref()],
        vec!["--inputs".as_ref(), path.as_os_str()],
        vec!["--input".as_ref(), path.as_os_str(), "extra".as_ref()],
        vec![path.as_os_str()],
    ] {
        let out = gate(&args);
        assert_eq!(out.status.code(), Some(2), "{args:?}");
        assert_eq!(error_kind(&out), "bad_invocation", "{args:?}");
    }
}
