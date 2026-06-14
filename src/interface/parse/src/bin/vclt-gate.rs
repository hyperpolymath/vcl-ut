// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! vclt-gate — VCL-total ↔ VeriSimDB admissibility gate (producer half).
//!
//! Contract: docs/vclt-gate-contract.adoc (frozen, v1).
//!
//! Reads a JSON request on stdin, lexes+parses the statement, calls
//! `decider::certified_level(stmt, schema)`, emits a JSON response on
//! stdout, and exits:
//!   0 — admissible (certified_level == requested_level)
//!   1 — inadmissible (verdict rendered, certified_level == -1)
//!   2 — gate error (bad/unsupported request, internal guard)
//!
//! Pure function of (statement, schema): no network, no filesystem,
//! no clock, no env-dependent behaviour beyond stdin/stdout/stderr.

#![deny(clippy::unwrap_used, clippy::expect_used)]

use serde_json::{json, Value};
use std::io::{self, Read};
use vcltotal_parse::schema::{FieldDef, ModalitySchema, VqlType};
use vcltotal_parse::{
    ast::{Agent, Modality, SafetyLevel, Statement, Transition, VclOp},
    certified_level, certified_transition_level, check_level_n, level_name, parse_op, OctadSchema,
};

fn main() {
    std::process::exit(run());
}

fn run() -> i32 {
    let mut input = String::new();
    if io::stdin().read_to_string(&mut input).is_err() {
        emit_gate_error("io_error", "failed to read stdin");
        return 2;
    }

    let req: Value = match serde_json::from_str(&input) {
        Ok(v) => v,
        Err(e) => {
            emit_gate_error("bad_request_json", &format!("invalid JSON: {e}"));
            return 2;
        }
    };

    let schema_version = match req.get("schema_version").and_then(Value::as_i64) {
        Some(v) => v,
        None => {
            emit_gate_error("bad_request_json", "missing or non-integer schema_version");
            return 2;
        }
    };
    if schema_version != 1 {
        emit_gate_error(
            "unsupported_version",
            &format!("schema_version {schema_version} is not supported (only 1)"),
        );
        return 2;
    }

    let stmt_text = match req.get("statement").and_then(Value::as_str) {
        Some(s) => s,
        None => {
            emit_gate_error("bad_request_json", "missing or non-string statement field");
            return 2;
        }
    };

    let schema = match req.get("schema") {
        Some(s) => match parse_schema(s) {
            Ok(sc) => sc,
            Err(msg) => {
                emit_gate_error("bad_schema", &msg);
                return 2;
            }
        },
        None => empty_schema(),
    };

    // S2: the gate routes the full `VclOp`. A leading MERGE/SPLIT/NORMALISE
    // is a consonance transition, certified by `certified_transition_level`
    // (NEVER the Statement certifier); any other verb is a relational query.
    let op = match parse_op(stmt_text) {
        Ok(o) => o,
        Err(e) => {
            let response = json!({
                "schema_version": 1,
                "admissible": false,
                "requested_level": 0,
                "certified_level": -1,
                "levels": [
                    {
                        "level": 0,
                        "name": "ParseSafe",
                        "status": "fail",
                        "reason": e.to_string()
                    }
                ],
                "reasons": [format!("L0 ParseSafe: {e}")]
            });
            println!("{}", response);
            return 1;
        }
    };

    let stmt = match op {
        VclOp::Query(s) => *s,
        VclOp::Transit(t) => return run_transition(&t, &schema),
    };

    let k = safety_level_to_u8(stmt.requested_level);
    let requested_level_int = i64::from(k);
    let cert = certified_level(&stmt, &schema);

    let levels = build_levels(&stmt, &schema, k);
    let admissible = cert != -1;
    let reasons: Vec<String> = levels
        .iter()
        .filter(|l| l["status"] == "fail")
        .filter_map(|l| {
            l["reason"].as_str().map(|r| {
                format!(
                    "L{} {}: {}",
                    l["level"],
                    l["name"].as_str().unwrap_or(""),
                    r
                )
            })
        })
        .collect();

    let response = json!({
        "schema_version": 1,
        "admissible": admissible,
        "requested_level": requested_level_int,
        "certified_level": cert,
        "levels": levels,
        "reasons": reasons
    });
    println!("{response}");

    if admissible {
        0
    } else {
        1
    }
}

/// S2 transition gate: certify a consonance transition via
/// `certified_transition_level` (the InjectionProof ceiling, 4, or -1) and
/// render a transition-shaped response. A transition has no L5+ ladder (no
/// result set), so the report names the single achievable rung plus the
/// verb, NOT the L1..L10 statement ladder. Exit codes match the statement
/// path: 0 admissible, 1 inadmissible.
fn run_transition(t: &Transition, schema: &OctadSchema) -> i32 {
    let cert = certified_transition_level(t, schema);
    let admissible = cert != -1;
    let (verb, subjects) = transition_shape(t);
    let level_entry = json!({
        "level": 4,
        "name": "InjectionProof",
        "status": if admissible { "pass" } else { "fail" }
    });
    let reasons: Vec<String> = if admissible {
        vec![]
    } else {
        vec![
            "transition inadmissible: self-merge / non-distinct outputs, or \
             evidence carries a raw string literal / type-incompatible comparison"
                .to_string(),
        ]
    };
    let response = json!({
        "schema_version": 1,
        "kind": "transition",
        "verb": verb,
        "subjects": subjects,
        "admissible": admissible,
        "requested_level": 4,
        "certified_level": cert,
        "levels": [level_entry],
        "reasons": reasons
    });
    println!("{response}");
    if admissible {
        0
    } else {
        1
    }
}

/// The verb tag + subject-handle list for a transition (response metadata).
fn transition_shape(t: &Transition) -> (&'static str, Vec<String>) {
    match t {
        Transition::Merge(l, r, into, _, _) => {
            ("MERGE", vec![l.0.clone(), r.0.clone(), into.0.clone()])
        }
        Transition::Split(from, ol, or_, _, _) => {
            ("SPLIT", vec![from.0.clone(), ol.0.clone(), or_.0.clone()])
        }
        Transition::Normalise(s, _, _) => ("NORMALISE", vec![s.0.clone()]),
    }
}

fn build_levels(stmt: &Statement, schema: &OctadSchema, k: u8) -> Vec<Value> {
    let mut out = Vec::new();
    let mut n: u8 = 1;
    while n <= k {
        let pass = check_level_n(n, stmt, schema);
        let name = level_name(n);
        let mut entry = json!({
            "level": n,
            "name": name,
            "status": if pass { "pass" } else { "fail" }
        });
        if !pass {
            let reason = level_failure_reason(n);
            entry["reason"] = Value::String(reason.to_string());
        }
        out.push(entry);
        n = n.saturating_add(1);
    }
    out
}

fn level_failure_reason(n: u8) -> &'static str {
    match n {
        1 => "referenced field not found in schema",
        2 => "WHERE clause contains incompatible type comparison",
        3 => "nullable field accessed without null guard in WHERE or HAVING",
        4 => "WHERE clause contains a raw string literal",
        5 => "SELECT item has unresolvable type (not in schema)",
        6 => "no LIMIT bound present",
        7 => "no effect declaration present",
        8 => "no version constraint present",
        9 => "no linear resource annotation present",
        10 => "epistemic clause malformed or has circular entailment",
        _ => "level check failed",
    }
}

fn safety_level_to_u8(l: SafetyLevel) -> u8 {
    l as u8
}

fn emit_gate_error(kind: &str, message: &str) {
    eprintln!("vclt-gate error [{kind}]: {message}");
    let resp = json!({
        "schema_version": 1,
        "error": { "kind": kind, "message": message }
    });
    println!("{resp}");
}

// ── Schema JSON parsing ────────────────────────────────────────────────────

fn empty_schema() -> OctadSchema {
    OctadSchema {
        graph: ms(Modality::Graph),
        vector: ms(Modality::Vector),
        tensor: ms(Modality::Tensor),
        semantic: ms(Modality::Semantic),
        document: ms(Modality::Document),
        temporal: ms(Modality::Temporal),
        provenance: ms(Modality::Provenance),
        spatial: ms(Modality::Spatial),
    }
}

fn ms(modality: Modality) -> ModalitySchema {
    ModalitySchema {
        modality,
        fields: Vec::new(),
    }
}

fn parse_schema(v: &Value) -> Result<OctadSchema, String> {
    Ok(OctadSchema {
        graph: parse_modality_schema(v, "graph", Modality::Graph)?,
        vector: parse_modality_schema(v, "vector", Modality::Vector)?,
        tensor: parse_modality_schema(v, "tensor", Modality::Tensor)?,
        semantic: parse_modality_schema(v, "semantic", Modality::Semantic)?,
        document: parse_modality_schema(v, "document", Modality::Document)?,
        temporal: parse_modality_schema(v, "temporal", Modality::Temporal)?,
        provenance: parse_modality_schema(v, "provenance", Modality::Provenance)?,
        spatial: parse_modality_schema(v, "spatial", Modality::Spatial)?,
    })
}

fn parse_modality_schema(
    v: &Value,
    key: &str,
    modality: Modality,
) -> Result<ModalitySchema, String> {
    match v.get(key) {
        None => Ok(ms(modality)),
        Some(obj) => {
            let fields_arr = match obj.get("fields").and_then(Value::as_array) {
                Some(a) => a,
                None => return Ok(ms(modality)),
            };
            let mut fields = Vec::new();
            for f in fields_arr {
                fields.push(parse_field_def(f)?);
            }
            Ok(ModalitySchema { modality, fields })
        }
    }
}

fn parse_field_def(v: &Value) -> Result<FieldDef, String> {
    let name = v
        .get("name")
        .and_then(Value::as_str)
        .ok_or("field missing 'name'")?
        .to_string();
    let ty_val = v.get("ty").ok_or("field missing 'ty'")?;
    let ty = parse_vql_type(ty_val)?;
    let nullable = v.get("nullable").and_then(Value::as_bool).unwrap_or(false);
    let indexed = v.get("indexed").and_then(Value::as_bool).unwrap_or(false);
    Ok(FieldDef {
        name,
        ty,
        nullable,
        indexed,
    })
}

/// Parse a `VqlType` from the contract's encoding:
/// - Nullary variants: bare string (`"TString"`, `"TInt"`, etc.)
/// - Parameterised variants: single-key object (`{"TVector": 384}`, etc.)
fn parse_vql_type(v: &Value) -> Result<VqlType, String> {
    match v {
        Value::String(s) => parse_nullary_type(s),
        Value::Object(map) if map.len() == 1 => match map.iter().next() {
            Some((key, inner)) => parse_parameterised_type(key, inner),
            None => Err("expected single-key object for VqlType, found empty object".to_string()),
        },
        other => Err(format!(
            "expected string or single-key object for VqlType, got {other}"
        )),
    }
}

fn parse_nullary_type(s: &str) -> Result<VqlType, String> {
    match s {
        "TString" => Ok(VqlType::TString),
        "TInt" => Ok(VqlType::TInt),
        "TFloat" => Ok(VqlType::TFloat),
        "TBool" => Ok(VqlType::TBool),
        "TBytes" => Ok(VqlType::TBytes),
        "TTimestamp" => Ok(VqlType::TTimestamp),
        "THash" => Ok(VqlType::THash),
        "TOctad" => Ok(VqlType::TOctad),
        "TAny" => Ok(VqlType::TAny),
        other => Err(format!("unknown nullary VqlType: {other:?}")),
    }
}

fn parse_parameterised_type(key: &str, inner: &Value) -> Result<VqlType, String> {
    match key {
        "TVector" => {
            let n = inner.as_u64().ok_or("TVector requires integer dimension")?;
            Ok(VqlType::TVector(n))
        }
        "TList" => Ok(VqlType::TList(Box::new(parse_vql_type(inner)?))),
        "TNull" => Ok(VqlType::TNull(Box::new(parse_vql_type(inner)?))),
        "TCommonKnowledge" => Ok(VqlType::TCommonKnowledge(Box::new(parse_vql_type(inner)?))),
        "TKnows" => {
            let arr = inner.as_array().ok_or("TKnows requires [agent, type]")?;
            if arr.len() != 2 {
                return Err("TKnows requires exactly 2 elements".to_string());
            }
            let agent = parse_agent(&arr[0])?;
            let ty = parse_vql_type(&arr[1])?;
            Ok(VqlType::TKnows(agent, Box::new(ty)))
        }
        "TBelieves" => {
            let arr = inner.as_array().ok_or("TBelieves requires [agent, type]")?;
            if arr.len() != 2 {
                return Err("TBelieves requires exactly 2 elements".to_string());
            }
            let agent = parse_agent(&arr[0])?;
            let ty = parse_vql_type(&arr[1])?;
            Ok(VqlType::TBelieves(agent, Box::new(ty)))
        }
        "TRecord" => {
            let arr = inner
                .as_array()
                .ok_or("TRecord requires [[name,type]] array")?;
            let mut fields = Vec::new();
            for pair in arr {
                let p = pair
                    .as_array()
                    .ok_or("TRecord entry must be [name, type]")?;
                if p.len() != 2 {
                    return Err("TRecord entry must be exactly [name, type]".to_string());
                }
                let name = p[0]
                    .as_str()
                    .ok_or("TRecord field name must be string")?
                    .to_string();
                let ty = parse_vql_type(&p[1])?;
                fields.push((name, ty));
            }
            Ok(VqlType::TRecord(fields))
        }
        other => Err(format!("unknown parameterised VqlType key: {other:?}")),
    }
}

fn parse_agent(v: &Value) -> Result<Agent, String> {
    match v {
        Value::String(s) => match s.as_str() {
            "ENGINE" => Ok(Agent::Engine),
            "VALIDATOR" => Ok(Agent::Validator),
            "FEDERATION" => Ok(Agent::Federation),
            other if other.starts_with("PROVER:") => Ok(Agent::Prover(other[7..].to_string())),
            other if other.starts_with("USER:") => Ok(Agent::User(other[5..].to_string())),
            other => Err(format!("unknown agent string: {other:?}")),
        },
        other => Err(format!("agent must be a string, got {other}")),
    }
}
