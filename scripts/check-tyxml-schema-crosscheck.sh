#!/usr/bin/env bash
# Pin-time cross-check of generated/tyxml-html-schema.tsv against an
# independent reading of the same .mli files through OCaml's own parser
# (compiler-libs). Compares (kind, line, module path, name) for every type
# and val row. Orchestration only: the Lean gate `lake exe tyxmlschema` is
# the deciding check; this script needs an opam switch with
# compiler-libs.common and is not run in CI.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d "${TMPDIR:-/tmp}/tyxml-xcheck.XXXXXX")"
trap 'rm -rf -- "$tmp"' EXIT
cd "$repo_root"
ocamlfind ocamlopt -package compiler-libs.common -linkpkg scripts/tyxml-schema-crosscheck.ml -o "$tmp/crosscheck" >/dev/null 2>&1
lib=vendor/tyxml-d2916535/lib
"$tmp/crosscheck" "$lib/html_types.mli" > "$tmp/types.ocaml.tsv"
"$tmp/crosscheck" "$lib/html_sigs.mli" > "$tmp/sigs.ocaml.tsv"
awk -F'\t' -v T="$tmp" '$1=="type"||$1=="val"{ f=($2=="lib/html_types.mli")?"types":"sigs"; print $1"\t"$3"\t"$5"\t"$6 > (T"/"f".lean.tsv") }' generated/tyxml-html-schema.tsv
diff "$tmp/types.ocaml.tsv" "$tmp/types.lean.tsv"
diff "$tmp/sigs.ocaml.tsv" "$tmp/sigs.lean.tsv"
echo "PASS tyxml schema cross-check: $(cat "$tmp/types.ocaml.tsv" "$tmp/sigs.ocaml.tsv" | wc -l | tr -d ' ') declarations agree between the OCaml parser and the Lean gate"
