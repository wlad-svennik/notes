#!/bin/sh
# Reassemble and integrity-check the exact proof-only ZIP.
set -eu
cd "$(dirname "$0")"
OUT=NF210_independence_proof_only_2026-11-05.zip
cat archive/part-*.bin > "$OUT"
printf '%s  %s\n' '502afdde1bdaac727531d5f22fa8f24828b37a09c2df9a66b657bb3c8f0faec8' "$OUT" | sha256sum -c -
unzip -t "$OUT" >/dev/null
unzip -n "$OUT"
printf 'Source extracted under nf210_formal/\n'
