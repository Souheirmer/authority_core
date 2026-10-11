#!/usr/bin/env bash
# Installs Rust (rustup) and the pinned Verus release + the toolchain it requires.
# Idempotent: safe to run at the start of every session.
set -euo pipefail

VERUS_VERSION="0.2026.10.04.426d8b0"
VERUS_TAG="release/${VERUS_VERSION}"
VERUS_ZIP="verus-${VERUS_VERSION}-x86-linux.zip"
VERUS_URL="https://github.com/verus-lang/verus/releases/download/${VERUS_TAG//\//%2F}/${VERUS_ZIP}"

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS="${ROOT}/.tools"
mkdir -p "$TOOLS"

# 1. Rust via rustup (static.rust-lang.org)
if ! command -v rustup >/dev/null 2>&1; then
  curl -sSfL https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init -o "$TOOLS/rustup-init"
  chmod +x "$TOOLS/rustup-init"
  "$TOOLS/rustup-init" -y --default-toolchain none --profile minimal
fi
export PATH="$HOME/.cargo/bin:$PATH"

# 2. Verus release (github.com)
if [ ! -x "$TOOLS/verus-x86-linux/verus" ]; then
  curl -sSfL "$VERUS_URL" -o "$TOOLS/$VERUS_ZIP"
  (cd "$TOOLS" && unzip -oq "$VERUS_ZIP")
fi
VERUS_DIR="$TOOLS/verus-x86-linux"

# 3. Toolchain required by this Verus release
TOOLCHAIN="$(cat "$VERUS_DIR/version.json" 2>/dev/null | sed -n 's/.*"toolchain": *"\([^" ]*\).*/\1/p' || true)"
if [ -z "$TOOLCHAIN" ]; then
  # fall back to parsing the message verus prints when the toolchain is missing
  TOOLCHAIN="$("$VERUS_DIR/verus" --version 2>&1 | grep -o 'rustup install [^ ]*' | awk '{print $3}' | head -1 || true)"
fi
if [ -n "$TOOLCHAIN" ]; then
  rustup toolchain install "$TOOLCHAIN" --profile minimal
fi

"$VERUS_DIR/verus" --version
echo "VERUS_DIR=$VERUS_DIR"
echo "TOOLCHAIN=$TOOLCHAIN"
