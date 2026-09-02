#!/usr/bin/env bash
# WP-7: regenerate the post-rename parity receipt and compare it byte-for-byte
# with the committed source receipt taken at the pre-rename commit named in
# generated/whatwg-parity.source.txt. Hygiene context numbers inside
# `_@.<module>.<n>._hygCtx` names derive from the module name and are
# normalised on both sides before comparison.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/whatwg-parity.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
cd "$repo_root"
lake build Whatwg WhatwgTest >/dev/null
PARITY_OUT="$tmp/after.tsv" lake env lean scripts/WhatwgParity.lean >/dev/null
# Runs of spaces are collapsed too: the pretty-printer wraps at a fixed width,
# so a longer or shorter prefix moves its line breaks without changing a token.
norm() { sed -E -e 's/(_@\.«(ROOT|TEST)»[A-Za-z0-9_.]*\.)[0-9]+(\._hygCtx)/\1N\3/g' -e 's/ {2,}/ /g' "$1"; }
norm "$tmp/after.tsv" > "$tmp/after.norm"
norm generated/whatwg-parity.source.tsv > "$tmp/source.norm"
if ! cmp -s "$tmp/after.norm" "$tmp/source.norm"; then
  echo "FAIL whatwg parity: the renamed tree differs from the source receipt" >&2
  diff "$tmp/source.norm" "$tmp/after.norm" | cut -c1-200 | head -20 >&2
  exit 1
fi
cp "$tmp/after.tsv" generated/whatwg-parity.tsv
echo "PASS whatwg parity: $(wc -l < generated/whatwg-parity.tsv | tr -d ' ') constants identical to $(cat generated/whatwg-parity.source.txt)"
