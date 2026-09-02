# Census authored inputs

This directory is authored input to the P1 specification-algorithm census, not
generated output. `Gates/Census.lean` reads it; `generated/` receives what the
generator writes. Nothing here may be produced by a tool.

`SPEC-MANIFEST.md` owns the disposition vocabulary and the section table these
files are seeded from. `docs/SPEC-COVERAGE.md` owns the row kinds, the row
format, and what a disposition does to the denominator. Neither is restated
here; this file records only the format of the three inputs and the places
where a line departs from a literal reading of the manifest table.

## Files

| File | Fields | Role |
| --- | --- | --- |
| `dispositions.tsv` | `<section id>` `<kind or *>` `<disposition>` | the disposition of every row in a section |
| `overrides.tsv` | `<row id>` `<disposition>` `<reason>` | the disposition of one row whose section does not describe it |
| `rules.tsv` | `<kebab name>` `<locator>` | authored `rule` rows; empty at P1 |

Fields are tab-separated. A line whose first non-space character is `#`, and a
blank line, are ignored.

## How a row gets its disposition

1. An override in `overrides.tsv` whose row id matches, if there is one.
2. Otherwise the row's heading ancestry is walked from the innermost `<h4>`
   outward through the `<h3>` to the `<h2>`. At each section a line for the
   row's own kind wins over that section's `*` line, and the first section
   with either line decides.
3. A row that neither reaches fails generation. The generator has no default
   and invents no disposition.

Both directions are checked. An entry in `dispositions.tsv` or
`overrides.tsv` that no row uses also fails generation, so an entry cannot
outlive the rows it was written for.

## Where these files depart from a literal reading of the manifest table

The manifest table is keyed by `<h2>` and `<h3>` section. Four groups of rows
need a finer key, and each departure is derived from a rule the manifest or the
root `AGENTS.md` already states rather than from a new policy.

- **Transfer sub-sections.** `rs-transfer`, `ws-transfer` and `ts-transfer` are
  `<h4>` sections inside the otherwise `owned` stream classes, and they state
  the transferable-streams protocol. The manifest refuses transferable streams
  and the root `AGENTS.md` representation rules refuse them with a refusal
  theorem, so these three sections are `refused`.
- **The underlying source, sink and transformer APIs.** The manifest names the
  `UnderlyingSource`, `UnderlyingSink` and `Transformer` dictionaries and their
  members `foreignBoundary` in its own prose, below the table. Those
  dictionaries are exactly the content of the `underlying-source-api`,
  `underlying-sink-api` and `transformer-api` sections.
- **The piping requirements.** The requirement bullets are stated inside the
  `ReadableStreamPipeTo` algorithm block, which sits under the `owned`
  `rs-all-abstract-ops`. The manifest dispositions the piping requirements and
  that reference algorithm `requirement`, so the `requirement` rows of
  `rs-abstract-ops` and the `op.readable-stream-pipe-to` row carry it.
- **Foreign internal slots.** Twelve `slot` rows name ECMAScript internals
  rather than streams state: the `ArrayBuffer` and `ArrayBufferView` slots the
  byte-stream algorithms read, and the promise and completion-record fields the
  algorithms branch on. The manifest names ArrayBuffer detachment
  `foreignBoundary`, and the root `AGENTS.md` representation rules put host
  runtime objects and promises outside stored content, so these rows are
  `foreignBoundary`. The three promise and completion-record rows are the
  weakest of the twelve and are flagged for ratification in `overrides.tsv`.

## Counting note

The manifest's P0 survey records 66 distinct internal slot names. Four of those
are Bikeshed bibliography citations rather than internal slots, so the census
carries 62 `slot` rows. `Gates/Census.lean` documents the mechanical rule that
separates the two.
