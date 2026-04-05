// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>

//! Criterion benchmarks for the VCL-total formatter and linter.
//!
//! Measures throughput of:
//! - Query formatting (simple / medium / complex queries)
//! - Lint validation throughput
//! - Round-trip pipeline (format then lint)

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use vcl_total::fmt::format_vqlut;
use vcl_total::lint::lint_vqlut;

// ============================================================================
// Sample queries
// ============================================================================

const SIMPLE_QUERY: &str = "SELECT id FROM users;";

const MEDIUM_QUERY: &str = concat!(
    "SELECT id, name, email\n",
    "FROM users\n",
    "WHERE active = true\n",
    "ORDER BY name\n",
    "LIMIT 100;"
);

const COMPLEX_QUERY: &str = concat!(
    "SELECT u.id, u.name, p.title, count(*) AS post_count\n",
    "FROM users u\n",
    "JOIN posts p ON u.id = p.user_id\n",
    "WHERE u.active = true\n",
    "  AND p.published = true\n",
    "  AND p.created_at > '2026-01-01'\n",
    "GROUP BY u.id, u.name, p.title\n",
    "HAVING count(*) > 5\n",
    "ORDER BY post_count DESC, u.name ASC\n",
    "LIMIT 50;"
);

/// Build a query with `n` SELECT lines to stress test scaling.
fn build_n_line_query(n: usize) -> String {
    (0..n)
        .map(|i| format!("SELECT col_{i} FROM table_{i};"))
        .collect::<Vec<_>>()
        .join("\n")
}

// ============================================================================
// Benchmark group: query parsing (formatting)
// ============================================================================

fn bench_query_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("query_parsing");

    group.bench_function("simple", |b| {
        b.iter(|| black_box(format_vqlut(black_box(SIMPLE_QUERY))))
    });

    group.bench_function("medium", |b| {
        b.iter(|| black_box(format_vqlut(black_box(MEDIUM_QUERY))))
    });

    group.bench_function("complex", |b| {
        b.iter(|| black_box(format_vqlut(black_box(COMPLEX_QUERY))))
    });

    for n in [10, 50, 100] {
        let query = build_n_line_query(n);
        group.bench_with_input(
            BenchmarkId::new("n_line_query", n),
            &query,
            |b, q| b.iter(|| black_box(format_vqlut(black_box(q.as_str())))),
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark group: lint validation throughput
// ============================================================================

fn bench_lint_validation(c: &mut Criterion) {
    let mut group = c.benchmark_group("lint_validation");

    group.bench_function("simple_with_semicolon", |b| {
        b.iter(|| black_box(lint_vqlut(black_box(SIMPLE_QUERY))))
    });

    group.bench_function("medium_mixed", |b| {
        b.iter(|| black_box(lint_vqlut(black_box(MEDIUM_QUERY))))
    });

    group.bench_function("complex_no_semicolons", |b| {
        // Strip semicolons to maximise lint work.
        let query = COMPLEX_QUERY.replace(';', "");
        b.iter(|| black_box(lint_vqlut(black_box(query.as_str()))))
    });

    for n in [10, 50, 100] {
        let query = build_n_line_query(n);
        group.bench_with_input(
            BenchmarkId::new("n_line_lint", n),
            &query,
            |b, q| b.iter(|| black_box(lint_vqlut(black_box(q.as_str())))),
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark group: round-trip pipeline (format then lint)
// ============================================================================

fn bench_round_trip_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("round_trip_pipeline");

    group.bench_function("simple_round_trip", |b| {
        b.iter(|| {
            let formatted = format_vqlut(black_box(SIMPLE_QUERY));
            black_box(lint_vqlut(black_box(&formatted)))
        })
    });

    group.bench_function("medium_round_trip", |b| {
        b.iter(|| {
            let formatted = format_vqlut(black_box(MEDIUM_QUERY));
            black_box(lint_vqlut(black_box(&formatted)))
        })
    });

    group.bench_function("complex_round_trip", |b| {
        b.iter(|| {
            let formatted = format_vqlut(black_box(COMPLEX_QUERY));
            black_box(lint_vqlut(black_box(&formatted)))
        })
    });

    group.bench_function("idempotent_double_format", |b| {
        b.iter(|| {
            let first  = format_vqlut(black_box(MEDIUM_QUERY));
            let second = format_vqlut(black_box(&first));
            black_box(second)
        })
    });

    group.finish();
}

// ============================================================================
// Criterion entry point
// ============================================================================

criterion_group!(
    benches,
    bench_query_parsing,
    bench_lint_validation,
    bench_round_trip_pipeline,
);
criterion_main!(benches);
