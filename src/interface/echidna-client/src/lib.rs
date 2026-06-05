// SPDX-License-Identifier: MPL-2.0

//! Async REST client for the echidna proof engine.
//!
//! Package 4 of the vcl-ut ↔ echidna binding: the transport layer. vcl-ut's
//! query compiler produces a plan; this client ships that plan to echidna
//! over HTTP and retrieves the resulting proof state. vcl-ut → echidna is
//! the default flow; reverse traffic (echidna importing vcl-ut Statements)
//! lives in a separate `ingress` crate.
//!
//! # Wire types vs core types
//!
//! Echidna's REST layer is a deliberate subset of its internal surface:
//! goals travel as prover-syntax `String`s rather than structured `Term`s,
//! proof scripts as `Vec<String>`, and the `ProverKind` exposed over REST
//! currently enumerates 17 of the 105 backends the dispatcher supports.
//! Translating a core `Term` into prover syntax is echidna's job, not ours.
//!
//! The [`wire`] module below therefore redeclares the REST envelope types
//! ([`ProofRequest`], [`ProofResponse`], [`TacticRequest`], [`TacticResponse`],
//! [`Tactic`], [`ProverInfo`], [`ProofStatus`], [`ProverKind`]) because
//! echidna's `interfaces/rest` workspace member keeps `models.rs` private
//! to its bin target. This is a duplication hazard flagged as TODO below —
//! the clean fix is either extracting `models.rs` into `echidna-core` or
//! splitting it into a new `echidna-rest-types` crate. Either is a
//! cross-repo change on echidna and is deferred until the Package 4 seam
//! is proven end-to-end.
//!
//! Core proof-surface types ([`core::Term`], [`core::Goal`],
//! [`core::ProofState`], [`core::Tactic`]) come from `echidna-core` via
//! [`vcltotal_interface`] re-exports and are used by callers that want to
//! work in structured form.

use thiserror::Error;

pub use vcltotal_interface::{core, types};

/// REST envelope types matching `echidna/src/interfaces/rest/models.rs`.
///
/// TODO(package-4): consolidate with echidna-side definitions. Two viable
/// moves: (a) promote these into `echidna-core` behind an optional `rest`
/// feature that gates the `utoipa::ToSchema` derives, or (b) split into a
/// new `echidna-rest-types` crate in the echidna workspace. Either ends
/// the drift risk that this redeclaration introduces.
pub mod wire {
    use serde::{Deserialize, Serialize};

    /// Mirror of echidna's REST-exposed ProverKind subset (17 backends).
    /// The core `ProverKind` in `echidna-core` has 105 variants; this is
    /// the smaller set the current REST handler accepts.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub enum ProverKind {
        Agda,
        Coq,
        Lean,
        Isabelle,
        Z3,
        Cvc5,
        Metamath,
        HolLight,
        Mizar,
        Pvs,
        Acl2,
        Hol4,
        Idris2,
        Vampire,
        EProver,
        Spass,
        AltErgo,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub enum ProofStatus {
        Pending,
        InProgress,
        Success,
        Failed,
        Timeout,
        Error,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ProverInfo {
        pub kind: ProverKind,
        pub version: String,
        pub tier: u8,
        pub complexity: u8,
        pub available: bool,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ProofRequest {
        pub goal: String,
        pub prover: ProverKind,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub timeout_seconds: Option<u64>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ProofResponse {
        pub id: String,
        pub prover: ProverKind,
        pub goal: String,
        pub status: ProofStatus,
        pub proof_script: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub time_elapsed: Option<f64>,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub error_message: Option<String>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct TacticRequest {
        pub name: String,
        pub args: Vec<String>,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct TacticResponse {
        pub success: bool,
        pub proof_state: ProofResponse,
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct Tactic {
        pub name: String,
        pub args: Vec<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub description: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        pub confidence: Option<f32>,
    }

    /// Cross-prover proof-exchange format. Mirrors
    /// `echidna::interfaces::rest::models::ExchangeFormat`.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(rename_all = "snake_case")]
    pub enum ExchangeFormat {
        /// OpenTheory — HOL-family cross-checking.
        OpenTheory,
        /// Dedukti / Lambdapi — λΠ-calculus-modulo.
        Dedukti,
    }

    /// Response body of `GET /api/v1/proofs/:id/export?format=...`.
    /// `content` is the JSON-serialized article or module — typed
    /// deserialization is the caller's choice.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ExportResponse {
        pub format: ExchangeFormat,
        pub content: serde_json::Value,
    }

    /// Body of `POST /api/v1/exchange/import`. `content` is a JSON-
    /// serialized OpenTheoryArticle or DeduktiModule.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ImportRequest {
        pub format: ExchangeFormat,
        pub content: serde_json::Value,
    }

    /// Response body of `POST /api/v1/exchange/import`. `proof_state`
    /// is the imported `ProofState` as JSON — round-trip tests compare
    /// this against an independently-derived reference.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct ImportResponse {
        pub proof_state: serde_json::Value,
    }
}

/// Client errors surfaced to callers. Wraps reqwest transport failures and
/// adds a few semantic variants for the status codes echidna's handler
/// layer returns (404 for unknown proof id, 4xx for malformed requests).
#[derive(Debug, Error)]
pub enum ClientError {
    #[error("http transport error: {0}")]
    Http(#[from] reqwest::Error),

    #[error("unexpected status {status}: {body}")]
    UnexpectedStatus {
        status: reqwest::StatusCode,
        body: String,
    },

    #[error("proof session not found: {0}")]
    NotFound(String),

    #[error("server rejected request ({status}): {body}")]
    BadRequest {
        status: reqwest::StatusCode,
        body: String,
    },

    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
}

/// Async REST client for echidna.
///
/// Construct with [`EchidnaClient::new`] (defaults to `http://127.0.0.1:8000`)
/// or [`EchidnaClient::with_base_url`] for a non-default host.
#[derive(Debug, Clone)]
pub struct EchidnaClient {
    base_url: String,
    http: reqwest::Client,
}

impl EchidnaClient {
    /// Client pointed at the default local echidna REST port.
    pub fn new() -> Self {
        Self::with_base_url("http://127.0.0.1:8000")
    }

    /// Client pointed at a specific `http://host:port` base (no trailing
    /// slash). Accepts anything `Into<String>` so callers can pass &str.
    pub fn with_base_url(base_url: impl Into<String>) -> Self {
        Self {
            base_url: base_url.into(),
            // No builder configuration is applied, so the canonical
            // infallible constructor is exact — and `Default for
            // EchidnaClient` requires construction to be infallible.
            http: reqwest::Client::new(),
        }
    }

    fn url(&self, path: &str) -> String {
        format!("{}{}", self.base_url, path)
    }

    /// GET /health — cheap reachability probe. Returns the literal "OK"
    /// that echidna's handler emits. Used by the matrix CI to skip jobs
    /// when the server is down.
    pub async fn health(&self) -> Result<String, ClientError> {
        let resp = self.http.get(self.url("/health")).send().await?;
        self.ok_or_err(resp).await?.text().await.map_err(Into::into)
    }

    /// GET /api/v1/provers — returns every prover the REST handler exposes.
    /// Note: this is the 17-variant REST subset, not all 105 backends.
    pub async fn list_provers(&self) -> Result<Vec<wire::ProverInfo>, ClientError> {
        let resp = self.http.get(self.url("/api/v1/provers")).send().await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// GET /api/v1/provers/:kind — one prover's info.
    pub async fn get_prover(
        &self,
        kind: wire::ProverKind,
    ) -> Result<wire::ProverInfo, ClientError> {
        let slug = serde_json::to_string(&kind)?
            .trim_matches('"')
            .to_string();
        let resp = self
            .http
            .get(self.url(&format!("/api/v1/provers/{}", slug)))
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// POST /api/v1/proofs — submit a goal and get a session back.
    ///
    /// Echidna runs the prover asynchronously; the returned `ProofResponse`
    /// carries the session id and initial status (usually `Pending` or
    /// `InProgress`). Poll with [`Self::get_proof`] or drive it via
    /// [`Self::apply_tactic`].
    pub async fn submit_proof(
        &self,
        req: &wire::ProofRequest,
    ) -> Result<wire::ProofResponse, ClientError> {
        let resp = self
            .http
            .post(self.url("/api/v1/proofs"))
            .json(req)
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// GET /api/v1/proofs/:id — poll an existing session.
    pub async fn get_proof(&self, id: &str) -> Result<wire::ProofResponse, ClientError> {
        let resp = self
            .http
            .get(self.url(&format!("/api/v1/proofs/{}", id)))
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// DELETE /api/v1/proofs/:id — cancel a session.
    pub async fn cancel_proof(&self, id: &str) -> Result<(), ClientError> {
        let resp = self
            .http
            .delete(self.url(&format!("/api/v1/proofs/{}", id)))
            .send()
            .await?;
        self.ok_or_err(resp).await?;
        Ok(())
    }

    /// POST /api/v1/proofs/:id/tactics — apply a tactic to an open session.
    pub async fn apply_tactic(
        &self,
        id: &str,
        tac: &wire::TacticRequest,
    ) -> Result<wire::TacticResponse, ClientError> {
        let resp = self
            .http
            .post(self.url(&format!("/api/v1/proofs/{}/tactics", id)))
            .json(tac)
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// GET /api/v1/proofs/:id/tactics/suggest — neural suggestions for
    /// the next move. Falls back to cosine-similarity when the Julia ML
    /// sidecar at :8090 is down (echidna's own fallback; we just receive
    /// the list).
    pub async fn suggest_tactics(&self, id: &str) -> Result<Vec<wire::Tactic>, ClientError> {
        let resp = self
            .http
            .get(self.url(&format!("/api/v1/proofs/{}/tactics/suggest", id)))
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// GET /api/v1/proofs/:id/export?format=... — export a session's
    /// current proof state to an OpenTheory article or Dedukti module.
    /// Returned `content` is the exporter's serde-serialized output;
    /// callers deserialize it into the concrete format type they need.
    pub async fn export_proof(
        &self,
        id: &str,
        format: wire::ExchangeFormat,
    ) -> Result<wire::ExportResponse, ClientError> {
        let slug = serde_json::to_string(&format)?
            .trim_matches('"')
            .to_string();
        let resp = self
            .http
            .get(self.url(&format!("/api/v1/proofs/{}/export", id)))
            .query(&[("format", &slug)])
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// POST /api/v1/exchange/import — import an OpenTheory article or
    /// Dedukti module and receive the resulting `ProofState` as JSON.
    /// Stateless — does not create a session. Used by round-trip tests
    /// and by clients with existing proof artefacts.
    pub async fn import_proof(
        &self,
        req: &wire::ImportRequest,
    ) -> Result<wire::ImportResponse, ClientError> {
        let resp = self
            .http
            .post(self.url("/api/v1/exchange/import"))
            .json(req)
            .send()
            .await?;
        self.ok_or_err(resp).await?.json().await.map_err(Into::into)
    }

    /// Map HTTP status codes to semantic errors. 2xx passes through, 404
    /// becomes [`ClientError::NotFound`], other 4xx become
    /// [`ClientError::BadRequest`], everything else
    /// [`ClientError::UnexpectedStatus`].
    async fn ok_or_err(&self, resp: reqwest::Response) -> Result<reqwest::Response, ClientError> {
        let status = resp.status();
        if status.is_success() {
            return Ok(resp);
        }
        let body = resp.text().await.unwrap_or_default();
        if status == reqwest::StatusCode::NOT_FOUND {
            Err(ClientError::NotFound(body))
        } else if status.is_client_error() {
            Err(ClientError::BadRequest { status, body })
        } else {
            Err(ClientError::UnexpectedStatus { status, body })
        }
    }
}

impl Default for EchidnaClient {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Smoke test: client construction and URL assembly. No network.
    #[test]
    fn url_assembly() {
        let c = EchidnaClient::with_base_url("http://localhost:8000");
        assert_eq!(c.url("/health"), "http://localhost:8000/health");
        assert_eq!(
            c.url("/api/v1/proofs/abc"),
            "http://localhost:8000/api/v1/proofs/abc"
        );
    }

    /// The wire enum must round-trip to the exact snake_case slugs
    /// echidna's handlers deserialize. Regression guard against future
    /// renaming drift.
    #[test]
    fn prover_kind_serializes_snake_case() {
        let cases = [
            (wire::ProverKind::HolLight, "hol_light"),
            (wire::ProverKind::EProver, "e_prover"),
            (wire::ProverKind::AltErgo, "alt_ergo"),
            (wire::ProverKind::Cvc5, "cvc5"),
            (wire::ProverKind::Z3, "z3"),
        ];
        for (kind, expected) in cases {
            let json = serde_json::to_string(&kind).unwrap();
            assert_eq!(json, format!("\"{}\"", expected));
        }
    }

    /// ProofRequest round-trip. Guards against field renames that would
    /// silently break deserialization on the echidna side.
    #[test]
    fn proof_request_round_trips() {
        let req = wire::ProofRequest {
            goal: "forall n, n + 0 = n".to_string(),
            prover: wire::ProverKind::Coq,
            timeout_seconds: Some(30),
        };
        let json = serde_json::to_string(&req).unwrap();
        let back: wire::ProofRequest = serde_json::from_str(&json).unwrap();
        assert_eq!(back.goal, req.goal);
        assert_eq!(back.prover, req.prover);
        assert_eq!(back.timeout_seconds, req.timeout_seconds);
    }
}
