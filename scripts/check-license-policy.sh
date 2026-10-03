#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# Enforce the licensing contract in .machine_readable/compliance/license-policy.toml.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
    echo "license-policy: run inside a Git checkout" >&2
    exit 2
}
cd "$ROOT"

# Split the marker so REUSE does not mistake the validator's search pattern
# for an SPDX declaration in this script's own source.
spdx_marker='SPDX-License-''Identifier'

POLICY=".machine_readable/compliance/license-policy.toml"
REUSE_MAP="REUSE.toml"
[[ -f "$POLICY" && -f "$REUSE_MAP" ]] || {
    echo "license-policy: missing $POLICY or $REUSE_MAP" >&2
    exit 2
}
command -v reuse >/dev/null 2>&1 || {
    echo "license-policy: install REUSE 6.2.0 (pipx install 'reuse[charset-normalizer]==6.2.0')" >&2
    exit 2
}

# Official REUSE lint checks path coverage, annotation/header collisions,
# copyright data, SPDX validity, and the presence of each license text.
reuse lint

# Keep this small policy file deliberately boring to parse: the official REUSE
# CLI validates the full TOML and resolves file-level annotations; these values
# supply the stricter, repository-specific allow-list below.
canonical_code="$(sed -n 's/^canonical_code = "\([^"]*\)"/\1/p' "$POLICY")"
canonical_docs="$(sed -n 's/^canonical_documentation = "\([^"]*\)"/\1/p' "$POLICY")"
max_headers="$(sed -n 's/^max_inline_spdx_headers = \([0-9][0-9]*\)$/\1/p' "$POLICY")"
scan_lines="$(sed -n 's/^header_scan_lines = \([0-9][0-9]*\)$/\1/p' "$POLICY")"
mapfile -t allowed_ids < <(
    sed -n 's/^allowed_spdx = \[\(.*\)\]$/\1/p' "$POLICY" \
        | grep -oE '"[A-Za-z0-9.+-]+"' \
        | tr -d '"'
)
mapfile -t forbidden_ids < <(
    sed -n 's/^forbidden_spdx = \[\(.*\)\]$/\1/p' "$POLICY" \
        | grep -oE '"[A-Za-z0-9.+-]+"' \
        | tr -d '"'
)
mapfile -t documentation_globs < <(
    sed -n 's/^documentation_globs = \[\(.*\)\]$/\1/p' "$POLICY" \
        | grep -oE '"[^"]+"' \
        | tr -d '"'
)
mapfile -t software_globs < <(
    sed -n 's/^software_globs = \[\(.*\)\]$/\1/p' "$POLICY" \
        | grep -oE '"[^"]+"' \
        | tr -d '"'
)

if [[ -z "$canonical_code" || -z "$canonical_docs" || -z "$max_headers" || -z "$scan_lines" || ${#allowed_ids[@]} -eq 0 || ${#documentation_globs[@]} -eq 0 || ${#software_globs[@]} -eq 0 ]]; then
    echo "license-policy: malformed policy contract: $POLICY" >&2
    exit 2
fi

is_allowed() {
    local candidate="$1" allowed
    for allowed in "${allowed_ids[@]}"; do
        [[ "$candidate" == "$allowed" ]] && return 0
    done
    return 1
}

matches_any_glob() {
    local candidate="$1" glob
    shift
    for glob in "$@"; do
        [[ "$candidate" == $glob ]] && return 0
    done
    return 1
}

# Do not let a relaxed or expanded config silently widen the license grant.
# Changes to either permitted license require an explicit edit to this gate.
expected_forbidden=("PMPL-1.0-or-later" "AGPL-3.0-only" "AGPL-3.0-or-later")
if (( ${#allowed_ids[@]} != 2 || ${#forbidden_ids[@]} != ${#expected_forbidden[@]} )) || ! is_allowed "$canonical_code" || ! is_allowed "$canonical_docs" || [[ "$canonical_code" == "$canonical_docs" ]]; then
    echo "license-policy: allowed/forbidden license set does not match the closed policy" >&2
    exit 2
fi
for expected in "${expected_forbidden[@]}"; do
    found=false
    for actual in "${forbidden_ids[@]}"; do
        [[ "$actual" == "$expected" ]] && found=true
    done
    [[ "$found" == true ]] || {
        echo "license-policy: policy contract must keep '$expected' forbidden" >&2
        exit 2
    }
done

errors=0
report_error() {
    printf 'license-policy: %s\n' "$1" >&2
    errors=$((errors + 1))
}

# Every SPDX header must be singular and use an approved SPDX identifier. REUSE
# lint below independently confirms each tracked file has exactly one effective
# license/copyright source through an inline header or the closed REUSE.toml map.
while IFS= read -r -d '' path; do
    [[ -f "$path" ]] || continue
    declarations="$(head -n "$scan_lines" "$path" | grep -aE "${spdx_marker}:[[:space:]]*[^[:space:]]+" || true)"
    file_license=""
    if [[ -n "$declarations" ]]; then
        count="$(printf '%s\n' "$declarations" | grep -c "${spdx_marker}:" || true)"
        if (( count > max_headers )); then
            report_error "$path has $count SPDX license headers in its first $scan_lines lines (maximum $max_headers)"
            continue
        fi
        while IFS= read -r declaration; do
            [[ -n "$declaration" ]] || continue
            identifier="$(printf '%s\n' "$declaration" | sed -E "s/.*${spdx_marker}:[[:space:]]*([^[:space:]*/]+).*/\\1/")"
            expression="$(printf '%s\n' "$declaration" | sed -E "s/.*${spdx_marker}:[[:space:]]*//; s/[[:space:]]*(-->|\\*\\)|\\*\\/)[[:space:]]*$//; s/[[:space:]]+$//")"
            file_license="$identifier"
            [[ "$expression" == "$identifier" ]] || report_error "$path must declare one SPDX identifier, not '$expression'"
            is_allowed "$identifier" || report_error "$path declares non-policy SPDX identifier '$identifier'"
        done <<< "$declarations"
    fi

    # Human-readable documentation is CC-BY-SA-4.0 by path policy. The explicit
    # tag makes this rule auditable without relying on annotation precedence.
    if matches_any_glob "$path" "${software_globs[@]}"; then
        [[ "$file_license" == "$canonical_code" ]] || report_error "$path must carry one $canonical_code SPDX header (found '${file_license:-none}')"
    elif matches_any_glob "$path" "${documentation_globs[@]}"; then
        [[ "$file_license" == "$canonical_docs" ]] || report_error "$path must carry one $canonical_docs SPDX header (found '${file_license:-none}')"
    fi
done < <(git ls-files --cached --others --exclude-standard -z)

# Check SPDX IDs attached to REUSE.toml annotation blocks as well. Path coverage,
# duplicate/overlapping metadata, and license-text validity are checked by REUSE.
while IFS= read -r declaration; do
    [[ -n "$declaration" ]] || continue
    identifier="$(printf '%s\n' "$declaration" | sed -E "s/.*${spdx_marker}[[:space:]]*=[[:space:]]*\"([^\"]+)\".*/\\1/")"
    is_allowed "$identifier" || report_error "$REUSE_MAP declares non-policy SPDX identifier '$identifier'"
done < <(grep -E "^[[:space:]]*${spdx_marker}[[:space:]]*=" "$REUSE_MAP" || true)

# Cargo's published package metadata must match the repository's code license.
while IFS= read -r -d '' manifest; do
    while IFS= read -r declared; do
        [[ -n "$declared" ]] || continue
        [[ "$declared" == "$canonical_code" ]] || report_error "$manifest declares Cargo license '$declared', expected '$canonical_code'"
    done < <(sed -n 's/^[[:space:]]*license[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' "$manifest")
done < <(git ls-files -z -- 'Cargo.toml' '**/Cargo.toml')

# The shipped license texts are a closed set and must match the permitted IDs.
for license_file in "$ROOT"/LICENSES/*.txt; do
    [[ -e "$license_file" ]] || continue
    identifier="$(basename "$license_file" .txt)"
    is_allowed "$identifier" || report_error "unused/non-policy license text: LICENSES/$identifier.txt"
done
for identifier in "${allowed_ids[@]}"; do
    [[ -f "$ROOT/LICENSES/$identifier.txt" ]] || report_error "missing license text: LICENSES/$identifier.txt"
done

if ! grep -q '^Mozilla Public License Version 2\.0$' LICENSE; then
    report_error "root LICENSE is not the canonical Mozilla Public License 2.0 text"
fi
if ! grep -q '"license"[[:space:]]*:[[:space:]]*{"id"[[:space:]]*:[[:space:]]*"MPL-2.0"}' .zenodo.json; then
    report_error ".zenodo.json must publish the canonical MPL-2.0 identifier"
fi

if (( errors != 0 )); then
    printf 'license-policy: failed with %d policy violation(s)\n' "$errors" >&2
    exit 1
fi
printf 'license-policy: passed (allowed SPDX IDs: %s; code: %s; docs: %s)\n' \
    "$(IFS=', '; echo "${allowed_ids[*]}")" "$canonical_code" "$canonical_docs"
