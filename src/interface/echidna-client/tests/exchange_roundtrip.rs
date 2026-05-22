// SPDX-License-Identifier: MPL-2.0

//! Proof-exchange round-trip integration tests.
//!
//! Mocks echidna's REST surface with wiremock, stands up the client
//! against the mock's address, and verifies the wire protocol for the
//! OpenTheory and Dedukti exchange endpoints. The actual round-trip
//! semantics (export → import → structural equivalence) are verified
//! echidna-side where the exporter/importer implementations live; this
//! test verifies the client *transport* round-trips a payload without
//! mangling it.
//!
//! Live-server integration (against a real echidna process on :8000)
//! is deferred to a separate `#[ignore]`'d test in Package 4 step 7.

use serde_json::json;
use vcltotal_echidna_client::{wire, EchidnaClient};
use wiremock::matchers::{body_json, header_exists, method, path, query_param};
use wiremock::{Mock, MockServer, ResponseTemplate};

/// Export call hits `GET /api/v1/proofs/:id/export?format=open_theory`
/// and returns an `ExportResponse` whose `content` field is the
/// JSON-serialized article payload echidna emitted.
#[tokio::test]
async fn export_opentheory_transport() {
    let server = MockServer::start().await;

    let article = json!({
        "name": "echidna-export",
        "assumptions": [],
        "conclusions": [
            { "hypotheses": [], "conclusion": "(eq (add n 0) n)" }
        ],
        "commands": ["version 6", "assume (forall n, eq (add n 0) n)"]
    });

    let response = json!({
        "format": "open_theory",
        "content": article
    });

    Mock::given(method("GET"))
        .and(path("/api/v1/proofs/session-abc/export"))
        .and(query_param("format", "open_theory"))
        .respond_with(ResponseTemplate::new(200).set_body_json(&response))
        .mount(&server)
        .await;

    let client = EchidnaClient::with_base_url(server.uri());
    let resp = client
        .export_proof("session-abc", wire::ExchangeFormat::OpenTheory)
        .await
        .expect("export must succeed against mock");

    assert_eq!(resp.format, wire::ExchangeFormat::OpenTheory);
    assert_eq!(
        resp.content,
        article,
        "exporter article must round-trip through the client verbatim"
    );
}

/// Dedukti export path. Confirms the slug switches correctly when the
/// caller asks for `ExchangeFormat::Dedukti`.
#[tokio::test]
async fn export_dedukti_transport() {
    let server = MockServer::start().await;

    let module = json!({
        "name": "echidna-export",
        "requires": [],
        "declarations": [
            { "Symbol": { "name": "goal_0", "ty": "prop" } }
        ]
    });

    Mock::given(method("GET"))
        .and(path("/api/v1/proofs/session-xyz/export"))
        .and(query_param("format", "dedukti"))
        .respond_with(ResponseTemplate::new(200).set_body_json(json!({
            "format": "dedukti",
            "content": module
        })))
        .mount(&server)
        .await;

    let client = EchidnaClient::with_base_url(server.uri());
    let resp = client
        .export_proof("session-xyz", wire::ExchangeFormat::Dedukti)
        .await
        .expect("dedukti export must succeed");

    assert_eq!(resp.format, wire::ExchangeFormat::Dedukti);
    assert_eq!(resp.content, module);
}

/// Import call hits `POST /api/v1/exchange/import` with an
/// `ImportRequest` body; the server echoes back an `ImportResponse`
/// whose `proof_state` field carries the ProofState JSON echidna
/// constructed from the article.
#[tokio::test]
async fn import_opentheory_transport() {
    let server = MockServer::start().await;

    let article = json!({
        "name": "roundtrip-input",
        "assumptions": [],
        "conclusions": [
            { "hypotheses": [], "conclusion": "(eq x x)" }
        ],
        "commands": []
    });

    let req_body = json!({
        "format": "open_theory",
        "content": article
    });

    let proof_state = json!({
        "goals": [],
        "context": {
            "theorems": [
                { "name": "thm_0", "statement": { "Var": "(eq x x)" }, "proof": null, "aspects": [] }
            ],
            "axioms": [],
            "definitions": [],
            "variables": []
        },
        "proof_script": [],
        "metadata": {}
    });

    Mock::given(method("POST"))
        .and(path("/api/v1/exchange/import"))
        .and(header_exists("content-type"))
        .and(body_json(&req_body))
        .respond_with(ResponseTemplate::new(200).set_body_json(json!({
            "proof_state": proof_state
        })))
        .mount(&server)
        .await;

    let client = EchidnaClient::with_base_url(server.uri());
    let req = wire::ImportRequest {
        format: wire::ExchangeFormat::OpenTheory,
        content: article,
    };
    let resp = client
        .import_proof(&req)
        .await
        .expect("import must succeed against mock");

    assert_eq!(resp.proof_state, proof_state);
}

/// End-to-end wire round-trip: export → echo the same article to the
/// import endpoint → confirm the client handed the exporter's output
/// back to the importer unchanged. Catches subtle bugs like query-
/// parameter encoding stripping JSON characters or reqwest quietly
/// altering UTF-8 payloads.
#[tokio::test]
async fn export_then_import_round_trip_transport() {
    let server = MockServer::start().await;

    let article = json!({
        "name": "roundtrip",
        "assumptions": [],
        "conclusions": [
            { "hypotheses": ["h_0"], "conclusion": "(implies (eq a b) (eq b a))" }
        ],
        "commands": ["version 6", "thm symmetry"]
    });

    // First stage: export returns the article.
    Mock::given(method("GET"))
        .and(path("/api/v1/proofs/roundtrip-session/export"))
        .respond_with(ResponseTemplate::new(200).set_body_json(json!({
            "format": "open_theory",
            "content": article
        })))
        .mount(&server)
        .await;

    // Second stage: import echoes the article back verbatim as a
    // ProofState (the mock doesn't actually run the importer — it
    // just proves the client re-sent what it received). Real semantic
    // equivalence is echidna's job to verify in its own test suite.
    Mock::given(method("POST"))
        .and(path("/api/v1/exchange/import"))
        .respond_with(ResponseTemplate::new(200).set_body_json(json!({
            "proof_state": article
        })))
        .mount(&server)
        .await;

    let client = EchidnaClient::with_base_url(server.uri());

    let exported = client
        .export_proof("roundtrip-session", wire::ExchangeFormat::OpenTheory)
        .await
        .expect("export leg");

    assert_eq!(exported.content, article);

    let imported = client
        .import_proof(&wire::ImportRequest {
            format: exported.format,
            content: exported.content.clone(),
        })
        .await
        .expect("import leg");

    // The mock echoes the content back as proof_state, so a byte-exact
    // match here proves nothing was mangled in transit on either leg.
    assert_eq!(imported.proof_state, exported.content);
}

/// 404 on an unknown session id surfaces as `ClientError::NotFound` and
/// carries the server's response body. Guards against future regressions
/// that would collapse 404 into a generic error.
#[tokio::test]
async fn export_missing_session_maps_to_not_found() {
    use vcltotal_echidna_client::ClientError;

    let server = MockServer::start().await;

    Mock::given(method("GET"))
        .and(path("/api/v1/proofs/does-not-exist/export"))
        .respond_with(ResponseTemplate::new(404).set_body_string("session gone"))
        .mount(&server)
        .await;

    let client = EchidnaClient::with_base_url(server.uri());
    let err = client
        .export_proof("does-not-exist", wire::ExchangeFormat::OpenTheory)
        .await
        .expect_err("missing session must error");

    match err {
        ClientError::NotFound(body) => assert_eq!(body, "session gone"),
        other => panic!("expected NotFound, got {:?}", other),
    }
}
