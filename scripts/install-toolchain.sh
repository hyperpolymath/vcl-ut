#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# install-toolchain.sh — install the *pinned* Zig for this repository, safely.
#
# WHY THIS EXISTS
#
# `build.zig` is version-sensitive, so the Zig version is a property of the
# repo, not of the machine: `.tool-versions` and `mise.toml` both pin it, and
# `.github/workflows/zig-shim-gate.yml` runs exactly that version. This script
# installs *that* pin, so a local `zig build test` reproduces CI instead of
# drifting with whatever `latest` happens to be.
#
# There is no official Zig `curl | sh` installer. Zig publishes versioned
# tarballs plus SHA-256 checksums in `https://ziglang.org/download/index.json`
# (and minisign signatures per file). This script downloads the tarball and
# verifies the checksum *before* extracting, and never pipes a remote script
# into a shell. If you have been given a `curl ... | sh` line for Zig, it is
# not from the Zig project — see `docs/developer/ABI-FFI-README.adoc`.
#
# METHODS
#
#   tarball  ziglang.org tarball, SHA-256 verified against index.json
#            (or a hash you supply with --sha256). Best on a normal machine.
#   pip      the `ziglang` wheel from PyPI (`pip install ziglang==<pin>`),
#            unpacked into --prefix. Use where PyPI is reachable but
#            ziglang.org is not (locked-down CI, some sandboxes).
#   auto     tarball, falling back to pip. The default.
#
# --from-file PATH installs a tarball you already downloaded (air-gapped or
# proxied networks). It still requires --sha256: the whole point is that
# nothing is extracted unverified.
#
# Rust (cargo) and Idris2 are *checked* but not installed: rustup and the
# Idris2 source build are not version-pinned in this repo the way Zig is, and
# silently installing a floating toolchain is the problem this script exists
# to avoid. --check prints what is missing and how to get it.
#
# Exit status: 0 on success (or when --check finds everything), 1 otherwise.
#
# Examples:
#   ./scripts/install-toolchain.sh --check
#   ./scripts/install-toolchain.sh                  # auto, into ~/.local/toolchains
#   ./scripts/install-toolchain.sh --method pip     # PyPI only
#   ./scripts/install-toolchain.sh --method tarball --sha256 <64 hex>
#   ./scripts/install-toolchain.sh --from-file ~/Downloads/zig-x86_64-linux-0.16.0.tar.xz \
#       --sha256 <64 hex>

set -eu

root=$(unset CDPATH; cd -- "$(dirname -- "$0")/.." && pwd)

prefix=${XDG_DATA_HOME:-$HOME/.local/toolchains}
method=auto
expected_sha=
from_file=
do_check=0
zig_url_base=https://ziglang.org/download

usage() {
    sed -n '3,45p' "$0" | sed 's/^# \{0,1\}//'
}

die() {
    echo "FAIL $*" >&2
    exit 1
}

info() {
    echo "  $*"
}

while [ $# -gt 0 ]; do
    case $1 in
        --check) do_check=1 ;;
        --prefix)
            shift
            [ $# -gt 0 ] || die "--prefix needs a directory"
            prefix=$1
            ;;
        --prefix=*) prefix=${1#*=} ;;
        --method)
            shift
            [ $# -gt 0 ] || die "--method needs auto|tarball|pip"
            method=$1
            ;;
        --method=*) method=${1#*=} ;;
        --sha256)
            shift
            [ $# -gt 0 ] || die "--sha256 needs a 64-hex digest"
            expected_sha=$1
            ;;
        --sha256=*) expected_sha=${1#*=} ;;
        --from-file)
            shift
            [ $# -gt 0 ] || die "--from-file needs a path"
            from_file=$1
            ;;
        --from-file=*) from_file=${1#*=} ;;
        -h|--help)
            usage
            exit 0
            ;;
        *) die "unknown argument: $1 (try --help)" ;;
    esac
    shift
done

case $method in
    auto|tarball|pip) ;;
    *) die "unknown --method '$method' (auto|tarball|pip)" ;;
esac

# ── The pin ───────────────────────────────────────────────────────────────
# `.tool-versions` is the machine-readable single source of truth here; it is
# what asdf/mise read, and notifying it is how CI's pin is kept honest.
pin_file="$root/.tool-versions"
[ -f "$pin_file" ] || die "missing $pin_file"
pinned_zig=$(awk '$1 == "zig" { print $2; exit }' "$pin_file")
[ -n "$pinned_zig" ] || die "no 'zig <version>' line in .tool-versions"

# ── Host detection ────────────────────────────────────────────────────────
os=$(uname -s)
arch=$(uname -m)

case "$os" in
    Linux) os_part=linux ;;
    Darwin) os_part=macos ;;
    *) die "unsupported OS '$os' (this script handles Linux and macOS; on Windows use the .zip from ziglang.org)" ;;
esac

case "$arch" in
    x86_64|amd64) arch_part=x86_64 ;;
    aarch64|arm64) arch_part=aarch64 ;;
    *) die "unsupported architecture '$arch'" ;;
esac

zig_key="$arch_part-$os_part"

# ── --check: report, change nothing ───────────────────────────────────────
version_of() {
    # version_of <cmd> — print the version, or nothing if the command is absent
    command -v "$1" >/dev/null 2>&1 || return 0
    "$1" version 2>/dev/null || "$1" --version 2>/dev/null || true
}

zig_local="$prefix/bin/zig"

if [ "$do_check" -eq 1 ]; then
    status=0
    echo "Pins ($pin_file): zig $pinned_zig"
    echo

    if [ -x "$zig_local" ]; then
        have=$("$zig_local" version 2>/dev/null || true)
        label="zig ($zig_local)"
    else
        have=$(command -v zig >/dev/null 2>&1 && zig version 2>/dev/null || true)
        label="zig (PATH)"
    fi
    if [ -z "$have" ]; then
        info "$label: NOT INSTALLED"
        info "  install: $0 --method auto"
        status=1
    elif [ "$have" = "$pinned_zig" ]; then
        info "$label: $have (matches pin)"
    else
        info "$label: $have — DOES NOT MATCH PIN $pinned_zig"
        info "  fix: $0 --method auto"
        status=1
    fi

    # rustc/cargo are build dependencies of the Zig artefacts (build.zig shells
    # cargo), not of the Zig code itself.
    for t in cargo rustc; do
        if command -v "$t" >/dev/null 2>&1; then
            info "$t: $(version_of "$t")"
        else
            info "$t: NOT INSTALLED — needed by 'zig build'/'zig build test'"
            status=1
        fi
    done

    # Idris2 is only needed for the ABI/proof gates.
    if command -v idris2 >/dev/null 2>&1; then
        info "idris2: $(idris2 --version 2>/dev/null | head -1)"
    else
        info "idris2: NOT INSTALLED (only needed for the proof-corpus/ABI gates)"
    fi

    if [ "$status" -ne 0 ]; then
        echo
        echo "Rust:   install from https://static.rust-lang.org/rustup/dist/ — verify the"
        echo "        published SHA-256, or use your distro's rustup package. There is no"
        echo "        pinned Rust version in this repo ('rust stable' in .tool-versions)."
        echo "Idris2: CI builds 0.8.0 from pinned source; see"
        echo "        .github/workflows/proof-corpus.yml for the exact steps."
    fi
    exit "$status"
fi

# ── Install ───────────────────────────────────────────────────────────────
pkg="$prefix/zig-$pinned_zig"
mkdir -p "$prefix/bin"

fetch() {
    # fetch <url> <dest>
    if command -v curl >/dev/null 2>&1; then
        curl --proto '=https' --tlsv1.2 -sSfL -o "$2" "$1"
    elif command -v wget >/dev/null 2>&1; then
        wget --https-only -q -O "$2" "$1"
    else
        die "need curl or wget to fetch $1"
    fi
}

sha256_of() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{ print $1 }'
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{ print $1 }'
    else
        die "need sha256sum or shasum -a 256 to verify the download"
    fi
}

# Top-level keys are `"<version>"` (quoted); inside a version block, platform
# keys are quoted too. We only look inside the block for the pinned version and
# then for our platform key, and we refuse anything that is not 64 hex chars —
# so a change of format fails closed rather than installing an unverified file.
shasum_from_index() {
    awk -v ver="$1" -v plat="$2" '
        BEGIN { inver = 0; indev = 0 }
        $0 ~ "\"" ver "\"[[:space:]]*:" { inver = 1; next }
        inver && /^[[:space:]]*}/ { inver = 0; indev = 0; next }
        inver && $0 ~ "\"" plat "\"[[:space:]]*:" { indev = 1; next }
        indev && /"shasum"[[:space:]]*:/ {
            line = $0
            sub(/.*"shasum"[[:space:]]*:[[:space:]]*"/, "", line)
            sub(/".*/, "", line)
            print line
            exit
        }'
}

install_tarball() {
    tarball="zig-$zig_key-$pinned_zig.tar.xz"
    tmpdir=$(mktemp -d)
    trap 'rm -rf "$tmpdir"' EXIT INT TERM

    want=$expected_sha
    if [ -n "$from_file" ]; then
        [ -f "$from_file" ] || die "no such file: $from_file"
        [ -n "$want" ] || die "--from-file needs --sha256 <digest>; the checksum is published at $zig_url_base/index.json and must be verified before extracting"
        cp "$from_file" "$tmpdir/$tarball"
    elif [ -z "$want" ]; then
        echo "==> fetching checksum list"
        index="$tmpdir/index.json"
        fetch "$zig_url_base/index.json" "$index" ||
            die "cannot reach $zig_url_base (network blocked?) — try --method pip"
        want=$(shasum_from_index "$pinned_zig" "$zig_key" < "$index" || true)
        case $want in
            [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]*)
                # cheap shape check, 64 hex enforced below
                len=$(printf '%s' "$want" | wc -c | tr -d ' ')
                [ "$len" -eq 64 ] || want=
                ;;
            *) want= ;;
        esac
        if [ -z "$want" ]; then
            die "could not read a SHA-256 for $zig_key $pinned_zig from index.json — refusing to install unverified. Re-run with --sha256 <digest> (the value is published at $zig_url_base/index.json)."
        fi
    fi

    if [ -z "$from_file" ]; then
        echo "==> downloading $tarball"
        fetch "$zig_url_base/$pinned_zig/$tarball" "$tmpdir/$tarball" ||
            die "download failed ($zig_url_base/$pinned_zig/$tarball) — try --method pip"
    else
        echo "==> using $from_file"
    fi

    echo "==> verifying SHA-256"
    got=$(sha256_of "$tmpdir/$tarball")
    if [ "$got" != "$want" ]; then
        die "checksum mismatch for $tarball
     expected $want
     got      $got
Refusing to install. Do not run a tarball whose hash does not match."
    fi

    echo "==> extracting to $pkg"
    rm -rf "$pkg.tmp"
    mkdir -p "$pkg.tmp"
    tar -xJf "$tmpdir/$tarball" -C "$pkg.tmp" --strip-components=1
    rm -rf "$pkg"
    mv "$pkg.tmp" "$pkg"
}

install_pip() {
    command -v python3 >/dev/null 2>&1 || die "--method pip needs python3"
    echo "==> pip install ziglang==$pinned_zig into $pkg"
    rm -rf "$pkg"
    python3 -m pip install --quiet --no-warn-script-location \
        --target "$pkg" "ziglang==$pinned_zig"
    # The wheel ships the compiler inside the package directory. Leave the
    # wheel's layout alone (the binary resolves its bundled lib/ relative to
    # itself) and expose it through the prefix with a symlink.
    found=$(find "$pkg" -maxdepth 2 -name zig -type f -perm -u+x | head -1)
    [ -n "$found" ] || die "the ziglang wheel did not contain a 'zig' executable"
    ln -sf "$found" "$prefix/bin/zig"
}

# Reachability probe, deliberately separate from install_tarball: `auto` must
# fall back to pip ONLY when the network is the problem. A checksum mismatch is
# not a fallback condition — it must abort the run, loudly. (An earlier draft
# ran `install_tarball 2>/dev/null || install_pip`, which would have hidden a
# tampered tarball behind a silent successful pip install.)
ziglang_org_reachable() {
    if command -v curl >/dev/null 2>&1; then
        curl --proto '=https' --tlsv1.2 -sSfI --max-time 15 \
            "$zig_url_base/index.json" -o /dev/null 2>/dev/null
    elif command -v wget >/dev/null 2>&1; then
        wget --https-only -q --spider --timeout=15 "$zig_url_base/index.json" 2>/dev/null
    else
        return 1
    fi
}

case $method in
    auto)
        if [ -n "$from_file" ] || ziglang_org_reachable; then
            install_tarball
        else
            echo "==> $zig_url_base unreachable; falling back to the PyPI wheel" >&2
            echo "    (set --method tarball to make this an error instead)" >&2
            install_pip
        fi
        ;;
    tarball) install_tarball ;;
    pip) install_pip ;;
esac

# Resolve `zig` through the prefix unless the tarball already put it there.
if [ ! -e "$prefix/bin/zig" ] && [ -x "$pkg/zig" ]; then
    ln -sf "$pkg/zig" "$prefix/bin/zig"
fi
[ -e "$prefix/bin/zig" ] || die "install finished but $prefix/bin/zig is missing"

have=$("$prefix/bin/zig" version 2>/dev/null || true)
[ "$have" = "$pinned_zig" ] || die "installed zig reports '$have', expected pin '$pinned_zig'"

cat <<EOF

Installed zig $have -> $prefix/bin/zig

Add it to PATH for this shell:

    export PATH="$prefix/bin:\$PATH"

Then, from the repo root:

    zig fmt --check ffi/zig/build.zig ffi/zig/src/lib.zig
    ./scripts/check-ffi-header.sh
    (cd ffi/zig && zig build test)     # also needs cargo

EOF
