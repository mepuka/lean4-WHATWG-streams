# Host conformance harnesses

This directory will contain the WPT replay harness and the decision-tape
replay harness. Harness output is evidence about a named host profile and
file set; it never defines the Lean semantics. `AGENTS.md` beside this file
owns the rules.

## Host profiles available on the P0 machine

| Profile | Version | Note |
| --- | --- | --- |
| Node `node:stream/web` | v22.23.2 | Windows 11 x86-64 |
| Bun | 1.4.0 | Windows 11 x86-64 |
| reference implementation under Node | `vendor/whatwg-streams-b9ba9f49/reference-implementation/` | requires its pinned npm dependencies; not installed at P0 |

Deno is not installed and is not a local profile. Browser engines enter only
through published WPT results cited by run identifier.

## P0 state

No harness exists yet. The first lands with P8.
