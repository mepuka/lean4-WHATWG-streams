# Web reification targets: a scored survey

R0-C survey, fetched 2026-09-01.

## 0. What this document is and is not

The operator asked for a brief survey identifying the top Lean reification
targets that would give the most expressivity and compatibility with web
programming in general. This is that survey. It is not specific to this
repository, and it establishes no semantic claim about any standard.

"Reification" here means what it means in `lean4-effect4`: a closed alphabet of
first-order operations with Lean semantics, proof graphs over those semantics,
and generated host code checked at exact pins. A target is a body of normative
text that could be reified that way.

Every external fact below carries the URL that was fetched and the fetch date.
Where a page could not be fetched, or where a number came back inconsistent
across fetches, that is said in place rather than papered over. Sentences that
rest on memory rather than a fetch are tagged INFERRED. Scores are judgments,
not measurements; the evidence sentence beside each cell is what can be checked.

All fetches in this document were made on 2026-09-01 unless a different date is
given. Some GitHub API reads returned timestamps of 2026-09-02 UTC; where that
matters the commit is named.

## 1. The rubric

Eight criteria, each scored 1 to 5, with fixed weights summing to 100. The
weighted total is the sum of score times weight, divided by 100, so it lands
back on the 1.00 to 5.00 scale.

| Code | Criterion | Weight | What a 5 looks like |
| --- | --- | ---: | --- |
| C1 | Normative tractability | 15 | Numbered algorithmic steps over named state, binding over any grammar |
| C2 | Test-corpus leverage | 15 | A large public conformance corpus in machine-readable form |
| C3 | Size and Lean tractability | 10 | Small, first-order, no host callbacks, no Unicode tables |
| C4 | Leverage over other targets | 15 | Many other candidates normatively depend on it |
| C5 | Expressivity unlocked | 15 | Yields total functions with round-trip and composition laws |
| C6 | Cross-runtime compatibility payoff | 15 | Named in ECMA-429 and shipped by every major runtime |
| C7 | Fit with Effect TypeScript | 8 | Effect v4 already exposes a module with this surface |
| C8 | Reuse of existing estate work | 7 | Directly reuses fips202, this repository, or its gate machinery |

The weights encode three priorities the question implies. Compatibility payoff
(C6), expressivity (C5), leverage (C4), tractability of the text (C1), and test
leverage (C2) are the load-bearing criteria at 15 each, because the operator
asked for expressive power and ecosystem compatibility. Size (C3) is worth 10:
it is a cost, not a benefit, and a large target with high leverage can still be
worth staging. Effect fit (C7) at 8 and estate reuse (C8) at 7 are tiebreakers,
because a target that is right on the merits does not become wrong because
Effect lacks a module for it.

Two scoring conventions, stated up front so the table is readable:

- C1 rewards *binding* algorithmic text. RFC 9651 scores 5 despite being an RFC
  because it says the algorithms bind and the ABNF is informative. RFC 8259
  scores lower despite being cleaner, because pure ABNF leaves the error
  behaviour that implementations actually disagree about unspecified.
- C6 is anchored to ECMA-429 membership, because that is the only published,
  citable, cross-runtime API list. Membership is worth 4 or 5; de facto
  ubiquity without membership caps at 3.

## 2. The candidate field

Forty candidates. Sizes are the specification *source* file where one exists,
because rendered page counts are unreliable (see the RFC 6455 row). WPT counts
are exact recursive blob counts against `web-platform-tests/wpt` at commit
`ae6982b121c5636392e003d839fd0eecb943db74`, read through the GitHub trees API
with `truncated=false` on every subtree
(https://github.com/web-platform-tests/wpt, fetched 2026-09-02).

### 2.1 WHATWG, W3C, and TC39 candidates

| # | Candidate | Source and form | Size | Conformance corpus | Reference impl | Depends on |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | **Infra** | https://infra.spec.whatwg.org/ — definitions, data structures, algorithmic prose. Last Updated 17 July 2026. 13 sections: primitive types, data structures, JSON, forgiving base64, namespaces | `infra.bs` 104,059 B (https://api.github.com/repos/whatwg/infra/contents/) | None of its own | No | Nothing |
| 2 | **Web IDL** | https://webidl.spec.whatwg.org/ — IDL grammar plus a highly algorithmic JavaScript binding section. Last Updated 31 August 2026 | `index.bs` 693,068 B (https://api.github.com/repos/whatwg/webidl/contents/) | WPT `webidl` 51 files; WPT `interfaces` 344 IDL files | No | Infra, ECMAScript |
| 3 | **Encoding** | https://encoding.spec.whatwg.org/ — decoder/encoder state machines over I/O queues, plus index tables. Last Updated 21 May 2026 | `encoding.bs` 145,368 B; index tables far larger (`index-gb18030.txt` 843,967 B, `indexes.json` 530,213 B) (https://api.github.com/repos/whatwg/encoding/contents/) | WPT `encoding` 340 files | No | Infra, Web IDL, Streams, HTML, Unicode |
| 4 | **URL** | https://url.spec.whatwg.org/ — an explicit named-state parser state machine (scheme start, authority, host, path, query, fragment, and more). Last Updated 18 August 2026 | `url.bs` 162,680 B (https://api.github.com/repos/whatwg/url/contents/) | WPT `url` 49 files, incl. `urltestdata.json` 228,685 B, `setters_tests.json` 82,134 B, `IdnaTestV2.json` 313,831 B, `toascii.json` 9,101 B (https://api.github.com/repos/web-platform-tests/wpt/contents/url/resources) | No | Infra, Encoding, UTS 46, Web IDL |
| 5 | **UTS 46 + Punycode** | https://www.unicode.org/reports/tr46/ rev 35, 2025-09-04, Unicode 17.0.0 — step-by-step ToASCII/ToUnicode plus a normative per-code-point mapping table; RFC 3492 gives pseudocode and a C reference implementation | Mapping table is the bulk; RFC 3492 is 35 pages | `IdnaTestV2.txt` per Unicode version; mirrored in WPT as `IdnaTestV2.json` 313,831 B | Yes (RFC 3492 Appendix C, C89) | Unicode Character Database, NFC |
| 6 | **MIME Sniffing** | https://mimesniff.spec.whatwg.org/ — extensively algorithmic; MIME type parse/serialize plus byte-pattern tables. Last Updated 17 July 2026 | `mimesniff.bs` 71,514 B (https://api.github.com/repos/whatwg/mimesniff/contents/) | Folded into WPT `fetch` and `html`; no dedicated top-level directory | No | Infra, Fetch, HTTP Semantics, Encoding, RFC 2046 |
| 7 | **Streams** | https://streams.spec.whatwg.org/ — algorithms over named internal slots; piping stated as requirements. Last Updated 18 August 2026 | `index.bs` 417,076 B (https://api.github.com/repos/whatwg/streams/contents/) | WPT `streams` 122 files; `readable-streams` alone is 22 files / 166,822 B (https://api.github.com/repos/web-platform-tests/wpt/contents/streams/readable-streams) | **Yes** — `reference-implementation/` with `lib/` and `run-web-platform-tests.js` (https://api.github.com/repos/whatwg/streams/contents/reference-implementation) | Infra, Web IDL, ECMAScript, DOM (AbortSignal), HTML |
| 8 | **Promise jobs + event loop** | https://html.spec.whatwg.org/multipage/webappapis.html §8.1.7, numbered algorithmic steps: task queues, microtask queue, agents, `HostEnqueuePromiseJob` (§8.1.6.6). ECMAScript side is `spec.html` | HTML `source` 7,905,796 B total (https://api.github.com/repos/whatwg/html/contents/); the event loop is a small fraction. ECMAScript `spec.html` 3,088,170 B (https://api.github.com/repos/tc39/ecma262/contents/) | WPT `html` 14,386 files, of which only ordering subsets are relevant | Engines only | ECMAScript |
| 9 | **DOM: AbortSignal subset** | https://dom.spec.whatwg.org/#aborting-ongoing-activities — numbered steps for abort algorithms, abort reason, dependent signals, `AbortSignal.any`/`timeout`. DOM Standard Last Updated 25 August 2026 | Section is roughly 2,500–3,000 words within `dom.bs` 476,405 B (https://api.github.com/repos/whatwg/dom/contents/) | Part of WPT `dom` 826 files | No | Infra, Web IDL, HTML (task queues) |
| 10 | **Fetch** | https://fetch.spec.whatwg.org/ — structured algorithmic steps, assertions, decision trees. Last Updated 1 September 2026 | `fetch.bs` 444,008 B (https://api.github.com/repos/whatwg/fetch/contents/) | WPT `fetch` 1,049 files | No | URL, Streams, Encoding, Infra, Web IDL, MIME Sniffing, HTML, HTTP Semantics, WebSockets, WebTransport |
| 11 | **Structured clone** | https://html.spec.whatwg.org/multipage/structured-data.html §2.7 — `StructuredSerialize`, `StructuredDeserialize`, `StructuredSerializeWithTransfer`, `structuredClone()`, all numbered steps; transfer is "irreversible and non-idempotent" | Within HTML `source` | WPT `html/webappapis/structured-clone` 7 files; `html/infrastructure/safe-passing-of-structured-data` 96 files | Engines only | ECMAScript, Web IDL |
| 12 | **Compression Streams** | https://github.com/whatwg/compression — thin spec wrapping deflate/gzip/brotli over TransformStream | `index.bs` **12,195 B** — the smallest WHATWG spec in this field (https://api.github.com/repos/whatwg/compression/contents/) | WPT `compression` 29 files | No | Streams, Web IDL |
| 13 | **Console** | https://console.spec.whatwg.org/ — algorithmic Logger/Formatter/Printer, format specifiers. Last Updated 15 March 2026 | Roughly 15,000–20,000 words | WPT `console` 16 files | No | Infra, Web IDL |
| 14 | **WebSockets (API)** | https://github.com/whatwg/websockets — the `WebSocket` IDL surface over RFC 6455 | `index.bs` 39,546 B (https://api.github.com/repos/whatwg/websockets/contents/) | WPT `websockets` 268 files | No | Fetch, RFC 6455, DOM |
| 15 | **File API** | https://w3c.github.io/FileAPI/ Editor's Draft 23 August 2026 — highly algorithmic: slice blob, package data, read operations | Roughly 150 KB of normative text (page statement, not a byte count) | WPT `FileAPI` 115 files | No | Infra, Streams, Web IDL, Encoding, MIME Sniffing, HTML, DOM, URL, Fetch |
| 16 | **Web Crypto** | https://w3c.github.io/webcrypto/ Level 2, W3C Editor's Draft 11 August 2026 — algorithmic steps over Web IDL types, but it **explicitly delegates the primitives**: the spec assumes user agents are not "directly implementing cryptographic operations" | Large; 18 top-level sections with a subsection per algorithm | WPT `WebCryptoAPI` 202 files | No | Web IDL, Infra, external crypto standards |
| 17 | **URLPattern** | https://github.com/whatwg/urlpattern — pattern matching over URL components | `spec.bs` 140,628 B (https://api.github.com/repos/whatwg/urlpattern/contents/) | WPT `urlpattern` 17 files — the smallest corpus of any ECMA-429 member | No | URL, Infra |
| 18 | **Server-Sent Events** | https://html.spec.whatwg.org/multipage/server-sent-events.html §9.2 — `EventSource`, `text/event-stream` with **both** an ABNF grammar and an explicit line-by-line parsing algorithm, plus reconnection | Roughly 3,500–4,000 words within HTML `source` | Within WPT `html` | Engines only | Fetch, HTML, DOM |
| 19 | **ArrayBuffer / TypedArray / DataView** | ECMAScript clause on structured data. **Could not fetch the clause body**: https://tc39.es/ecma262/multipage/structured-data.html and the `#sec-json-object` anchor both returned only the navigation table of contents, truncated before the clause. INFERRED from memory that this is clause 25 and that JSON.parse/stringify are given as numbered abstract operations | `spec.html` 3,088,170 B whole-spec | Engine test262 (not fetched) | Engines only | ECMAScript |
| 20 | **JSON.parse / JSON.stringify** | Same clause and same failed fetch as #19. The wire grammar is RFC 8259; the ECMAScript layer adds reviver/replacer and property ordering | Within `spec.html` | JSONTestSuite `test_parsing` ~300+ files with `y_`/`n_`/`i_` prefixes for must-accept, must-reject, and implementation-defined (https://api.github.com/repos/nst/JSONTestSuite/contents/test_parsing) | Engines only | ECMAScript, RFC 8259 |
| 21 | **String / UTF-16 semantics** | ECMAScript strings are sequences of UTF-16 code units, including lone surrogates. **This is a modelling hazard, not a target**: Lean's `String` is "a sequence of Unicode scalar values" stored as UTF-8, and `String.Pos` is "a byte offset ... together with a proof that this position is at a UTF-8 character boundary" (https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/) | n/a | test262 | n/a | ECMAScript |
| 22 | **HTML parser / fragment parsing** | HTML tokenizer and tree construction, in the HTML Standard | Within `source` 7,905,796 B; the parser is the largest single algorithm on the web platform | WPT `html` 14,386 files plus html5lib-tests | Engines only | Infra, DOM, Encoding |
| 23 | **FormData (XHR)** | The `FormData` interface, owned by the XMLHttpRequest Standard, required by ECMA-429 | Within the XHR standard | WPT `xhr` 445 files | No | Infra, Web IDL, RFC 7578 |
| 24 | **ECMA-429 Minimum common web API** | https://ecma-international.org/publications-and-standards/standards/ecma-429/ — "Minimum common web API", 1st edition, December 2025, TC55. Editor's draft at https://min-common-api.proposal.wintertc.org/ (draft of 31 July 2026). A *list*, not an algorithmic spec: it names 45 interfaces plus ~26 globals and delegates every definition | `index.bs` 16,155 B | n/a — it is a compatibility lens | n/a | All of the above |

### 2.2 IETF candidates

| # | Candidate | Source and form | Size | Test vectors | Notes |
| --- | --- | --- | --- | --- | --- |
| 25 | **RFC 3986 URI** | https://www.rfc-editor.org/rfc/rfc3986.html — Internet Standard **STD 66**, January 2005. ABNF-primary, with one real algorithm: §5.2.4 `remove_dot_segments` | ~60 pages | **Yes** — §5.4.1 ~26 normal and §5.4.2 ~18 abnormal reference-resolution pairs, ~44 total | Obsoletes 2396, 2732, 1808. Distinct from the WHATWG URL Standard, which is a state machine and is what browsers implement |
| 26 | **RFC 9110 HTTP Semantics** | https://www.rfc-editor.org/rfc/rfc9110.html — Internet Standard **STD 97**, June 2022. Predominantly 2119 prose plus ABNF for field syntax; algorithms are narrative, not numbered | 19 sections + appendices A–E; page count not surfaced by any of three fetches | **None** | Obsoletes 7230 in part, 7231, 7232, 7233, 7235, and others |
| 27 | **RFC 9112 HTTP/1.1 syntax** | https://www.rfc-editor.org/rfc/rfc9112.html — Internet Standard **STD 99**, June 2022. ABNF plus §7.1.3 chunked decoding as pseudo-code | 13 sections + appendices A–C; page count reported only as "80+", unconfirmed | **None** — embedded examples only | **Updated by RFC 9931**, a post-publication update to HTTP/1.1 syntax |
| 28 | **RFC 9111 HTTP Caching** | https://www.rfc-editor.org/rfc/rfc9111.html — Internet Standard **STD 98**, June 2022. Prose plus ABNF plus genuine arithmetic: `current_age = corrected_initial_age + resident_time` | 9 sections + 5 appendices | Essentially none | Obsoletes RFC 7234 (Proposed Standard, 43 pages) |
| 29 | **RFC 9651 Structured Fields** | https://www.rfc-editor.org/rfc/rfc9651.html and https://httpwg.org/specs/rfc9651.html — Proposed Standard, September 2024. **Algorithm-normative**: "implementations MUST have behavior that is indistinguishable from following the algorithms", with Appendix C ABNF explicitly informative | 7 sections + 4 appendices | **External and machine-readable** — https://api.github.com/repos/httpwg/structured-field-tests/contents/ holds 25 JSON test files plus `serialisation-tests/`, including generated files up to 727 KB | **Obsoletes RFC 8941.** Items, lists, dictionaries, parameters, dates, display strings |
| 30 | **Cookies** | https://datatracker.ietf.org/doc/draft-ietf-httpbis-rfc6265bis/ — **still an Internet-Draft, no RFC number**: draft-22, 2025-12-01, expired 2026-06-04, in the RFC Editor queue. ABNF plus heavy step-by-step algorithms (§5.1.1 date parsing, §5.6 Set-Cookie processing) | Draft | No vector appendix | **A successor to the successor exists**: draft-ietf-httpbis-layered-cookies-02 (2026-05-21) declares it obsoletes "RFC 6265 and 6265bis". There is no stable normative citation for cookies today |
| 31 | **RFC 6455 WebSocket** | https://www.rfc-editor.org/rfc/rfc6455.html — Proposed Standard, December 2011. Four normative forms at once: ABNF, numbered handshake algorithms, ASCII bit-diagram framing, and 2119 prose | **Page count unresolved** — three fetches returned 39, 73, and 98; all summariser inferences from footer markers. Do not cite a page count without a manual check | **Yes** — ~15–20 examples including the `Sec-WebSocket-Accept` GUID computation with hex output, masking-key and fragmentation examples | Updated by RFC 7936, 8307, 8441. Normatively cites the obsolete RFC 2616 |
| 32 | **RFC 8259 JSON** | https://www.rfc-editor.org/rfc/rfc8259.html — Internet Standard **STD 90**, December 2017. Almost purely ABNF, thin prose, no algorithms | **16 pages** (confirmed via datatracker) | **None** — ~5 illustrative documents; the real interop suites are external and non-normative | Obsoletes 7159 |
| 33 | **RFC 8949 CBOR** | https://www.rfc-editor.org/rfc/rfc8949.html — Internet Standard **STD 94**, December 2020. Prose plus tables plus pseudocode; §8 defines a diagnostic notation | 11 sections + appendices A–G | **Strongest in the field** — Appendix A is a value-to-hex table of roughly 80 entries, Appendix B is a complete 256-row jump table for every possible initial byte | Obsoletes 7049 |
| 34 | **RFC 4648 Base16/32/64** | https://www.rfc-editor.org/rfc/rfc4648.html — Proposed Standard, October 2006. **No ABNF at all**: prose algorithm, five alphabet tables, bit-mapping illustrations | **18 pages** (confirmed) | **Yes** — §10 is literally titled "Test Vectors": 21 vectors across BASE64, BASE32, and BASE32-HEX over prefixes of "foobar" | Only two normative dependencies: RFC 20 and RFC 2119. Note WHATWG defines its own *forgiving* base64 in Infra, which is not the same function |
| 35 | **RFC 7578 multipart/form-data** | https://www.rfc-editor.org/rfc/rfc7578.html — July 2015. **Prose requirements only — no grammar, no algorithm.** The weakest normative form in the field, governing one of the most-implemented wire formats on the web | 9 sections + 2 appendices, ~15 pages | **None** — 3 or 4 scattered fragments | Obsoletes RFC 2388. Builds on RFC 2046 (~42 pages, RFC 822-style BNF) |
| 36 | **JOSE: RFC 7515 / 7519 / 7518** | All Proposed Standard, May 2015. **7515 (JWS)** is the strong one: https://www.rfc-editor.org/rfc/rfc7515.html gives §5.1 signing as 8 numbered steps and §5.2 validation as 10. **7519 (JWT)** is prose. **7518 (JWA)** is algorithm descriptions plus registry tables | 7519 is **30 pages** (confirmed); 7518 is 69 pages; 7515 page count conflicted across fetches (47 vs 58), unresolved | **Yes** — 7515 Appendix A has 7 worked examples with full base64url intermediates; 7518 Appendix B has AES_CBC_HMAC_SHA2 vectors and Appendix C a worked ECDH-ES computation; 7519 Appendix A has 2 | 7519 is updated by RFC 7797 and RFC 8725 |
| 37 | **Media types: RFC 2045 / 6838** | https://www.rfc-editor.org/rfc/rfc2045.html (31 pages, RFC 822-style BNF) and https://www.rfc-editor.org/rfc/rfc6838.html (**BCP 13**, 32 pages, ABNF for names plus procedural registration prose) | 31 and 32 pages | None applicable | 6838 is a process document, not a wire-format spec. The parsing that matters is in MIME Sniffing (#6) |
| 38 | **RFC 2397 data URLs** | https://www.rfc-editor.org/rfc/rfc2397.html — August 1998. **Three BNF productions in total.** INFERRED that its maturity is Proposed Standard; the fetch confirmed only the "Standards Track" category line | **5 pages** — the smallest candidate in the field | No; 4 illustrative examples | Normatively cites RFC 2396, obsoleted by 3986, and RFC 1866, obsolete. The Fetch Standard re-specifies data: URLs algorithmically in its own §7 |
| 39 | **RFC 9457 Problem Details** | https://www.rfc-editor.org/rfc/rfc9457.html — Proposed Standard, July 2023. Prose member definitions backed by a JSON Schema (Appendix A) and RELAX NG (Appendix B) | 7 sections + appendices A–D | None; 5 or 6 detailed examples | Obsoletes RFC 7807 |
| 40 | **RFC 9113 HTTP/2** | https://www.rfc-editor.org/rfc/rfc9113.html — Standards Track, June 2022. Prose, a stream-lifecycle state machine, and binary frame layouts | ~10 major sections, 60+ subsections | None named in the document | Obsoletes 7540 and 8740. Listed to be **rejected**: connection-level binary multiplexing has no ECMA-429 surface and no JS-visible semantics to compile to |

### 2.3 Dependency edges, condensed

Reading the "Depends on" columns together gives the substrate order. Infra has
no dependencies and everything depends on it. Web IDL depends only on Infra and
ECMAScript. Encoding depends on Infra, Web IDL, and Streams. URL depends on
Infra, Encoding, and UTS 46. Streams depends on Infra, Web IDL, ECMAScript, and
DOM for `AbortSignal`. Fetch sits on top of all of them and adds MIME Sniffing,
HTML, and HTTP Semantics — ten normative dependencies, the deepest in the field.
File API depends on nine. That shape decides the programs in section 4.

## 3. The ranked table

Scores are 1–5 per criterion, weighted as in section 1. Evidence for each score
is the corresponding row in section 2; the notes column carries the single fact
that most moved the total.

Sorted by weighted total, descending. Every total was recomputed by hand from the
weights in section 1.

| Rank | Candidate | C1 15 | C2 15 | C3 10 | C4 15 | C5 15 | C6 15 | C7 8 | C8 7 | **Total** | What decided it |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | **URL** | 5 | 5 | 4 | 4 | 5 | 5 | 4 | 3 | **4.53** | A named-state parser plus 228,685 B of `urltestdata.json`. Total functions with round-trip theorems, and an ECMA-429 member |
| 2 | **Encoding (UTF-8 core)** | 5 | 5 | 3 | 5 | 4 | 5 | 3 | 5 | **4.49** | Decoder state machines, 340 WPT files, and fips202 already carries the byte and bit machinery. Scoped to UTF-8; the legacy index tables are the cost |
| 3 | **Streams** | 5 | 4 | 2 | 3 | 5 | 5 | 5 | 5 | **4.25** | Algorithms over named slots, a reference implementation, 122 WPT files, and Effect's `Stream`/`Channel`/`Sink`. Size is the only weak cell |
| 4 | **Base64 (RFC 4648)** | 4 | 4 | 5 | 3 | 4 | 4 | 5 | 5 | **4.10** | 18 pages, 21 in-document vectors, `Effect.Encoding` already exposes the exact surface, and `atob`/`btoa` are ECMA-429 members |
| 5 | **Promise jobs + event loop** | 5 | 2 | 3 | 5 | 5 | 4 | 4 | 4 | **4.05** | FIFO, deterministic, and the thing every settlement-order theorem needs. Corpus score is low because the relevant WPT subset is buried in 14,386 files |
| 6 | **Infra** | 5 | 1 | 5 | 5 | 4 | 5 | 3 | 4 | **4.02** | 104 KB, no dependencies, everything depends on it; forgiving base64 and JSON live here. Loses only on having no corpus of its own |
| 7 | **AbortSignal (DOM subset)** | 5 | 3 | 5 | 3 | 4 | 5 | 4 | 2 | **3.96** | ~3,000 words, ECMA-429 member, and the interruption boundary this repository already treats as foreign. Dependent signals and `any` are real algebra |
| 8 | **Fetch** | 5 | 5 | 1 | 2 | 5 | 5 | 5 | 1 | **3.87** | The expressivity prize and the compatibility prize, at 444 KB with ten normative dependencies. Not a starting target; an ending one |
| 9 | **JSON wire grammar (RFC 8259)** | 3 | 4 | 5 | 3 | 4 | 4 | 4 | 3 | **3.73** | 16 pages of ABNF, ~300 external classification tests. Downgraded on C1: the RFC leaves the disagreements to the `i_` cases |
| 10 | **Structured Fields (RFC 9651)** | 5 | 5 | 4 | 2 | 5 | 2 | 3 | 2 | **3.63** | The only IETF spec that says its algorithms bind and its ABNF does not, with 25 external JSON test files. Held back by C6: no ECMA-429 surface |
| 11 | **JSON.parse/stringify (ECMAScript layer)** | 4 | 4 | 4 | 2 | 4 | 4 | 4 | 3 | **3.63** | Reviver, replacer, and property ordering are where the RFC stops and the observable behaviour starts. Scored on a **failed fetch** — see below |
| 12 | **ArrayBuffer / DataView** | 4 | 3 | 3 | 4 | 3 | 4 | 3 | 4 | **3.52** | Byte-level substrate for BYOB readers and every codec. Also scored on a **failed fetch** |
| 13 | **Web IDL (binding subset)** | 4 | 3 | 2 | 5 | 3 | 5 | 2 | 2 | **3.50** | Every other candidate's type conversions route through it, and 344 machine-readable IDL files exist. 693 KB and deep ECMAScript coupling are the cost |
| 14 | **MIME Sniffing** | 5 | 3 | 4 | 3 | 4 | 3 | 3 | 2 | **3.48** | 71 KB, extensively algorithmic, and MIME type parsing is a prerequisite for Fetch, File API, and Effect's `Mime.ts` |
| 15 | **structuredClone** | 5 | 3 | 3 | 2 | 4 | 5 | 2 | 2 | **3.45** | ECMA-429 member with cycle-preserving graph semantics; transfer is "irreversible and non-idempotent", which is a law worth having |
| 16 | **Web IDL (full surface)** | 4 | 3 | 1 | 5 | 3 | 5 | 2 | 2 | **3.40** | Listed separately from row 13 to make the point that the binding subset is tractable and the whole thing is not |
| 17 | **File API (Blob)** | 5 | 3 | 3 | 2 | 3 | 5 | 3 | 2 | **3.38** | ECMA-429 member, algorithmic, and `Blob.stream()` connects directly to Streams |
| 18 | **UTS 46 + Punycode** | 4 | 5 | 2 | 3 | 3 | 4 | 1 | 2 | **3.27** | `IdnaTestV2.txt` is the best conformance file in the survey, but the normative mapping table is a per-code-point Unicode database |
| 19 | **CBOR (RFC 8949)** | 4 | 5 | 4 | 1 | 5 | 1 | 2 | 4 | **3.24** | Appendix B's 256-row initial-byte table is a formal specification in disguise. Zero web-platform compatibility payoff |
| 20 | **Web Crypto** | 3 | 4 | 2 | 1 | 3 | 5 | 2 | 5 | **3.11** | 202 WPT files and fips202 already proves SHA3-512, but the spec explicitly delegates the primitives, so the interesting content is elsewhere |
| 21 | **JOSE (RFC 7515)** | 5 | 4 | 3 | 1 | 4 | 1 | 2 | 4 | **2.99** | 8-step signing and 10-step validation with 7 fully-worked appendix examples. No platform surface |
| 22 | **String / UTF-16 semantics** | 3 | 3 | 2 | 4 | 2 | 4 | 2 | 3 | **2.97** | **Not a target.** A constraint every other target inherits — see the caveat below |
| 23 | **Compression Streams** | 3 | 3 | 5 | 1 | 2 | 4 | 3 | 2 | **2.83** | 12,195 B is the smallest WHATWG spec here, but it delegates the actual codecs, so a Lean model would be a thin wrapper over an unmodelled core |
| 24 | **Server-Sent Events** | 5 | 2 | 5 | 1 | 3 | 1 | 4 | 3 | **2.83** | A genuine line-by-line stream parser with both ABNF and an algorithm, and Effect has `unstable/encoding/Sse.ts`. Not in ECMA-429 |
| 25 | **WebSockets API** | 4 | 4 | 4 | 1 | 3 | 2 | 3 | 1 | **2.81** | 39 KB over 268 WPT files; de facto ubiquitous, de jure absent from ECMA-429 |
| 26 | **FormData** | 3 | 3 | 4 | 1 | 2 | 5 | 3 | 1 | **2.81** | An ECMA-429 member whose own spec note says the constructor arguments are "not well-defined by this Standard" |
| 27 | **URLPattern** | 4 | 2 | 3 | 1 | 3 | 4 | 4 | 1 | **2.79** | An ECMA-429 member with only 17 WPT files and still experimental in Node. Cheap to model, weakly tested |
| 28 | **WebSocket protocol (RFC 6455)** | 4 | 4 | 2 | 1 | 4 | 1 | 3 | 3 | **2.75** | Four normative forms at once and good vectors, but not an ECMA-429 member and its page count could not even be resolved |
| 29 | **HTTP/1.1 syntax (RFC 9112)** | 3 | 1 | 3 | 2 | 5 | 2 | 4 | 2 | **2.71** | Chunked decoding is a real algorithm and message-framing theorems are the request-smuggling story, but there are no vectors at all |
| 30 | **ECMA-429 itself** | 1 | 1 | 5 | 5 | 1 | 5 | 2 | 1 | **2.68** | **Not a target.** It defines nothing; it is the compatibility lens the C6 column is scored against |
| 31 | **HTML parser** | 4 | 5 | 1 | 2 | 3 | 2 | 1 | 1 | **2.65** | The largest algorithm on the platform, with the best corpus. Out of reach for a first programme |
| 32 | **HTTP Semantics (RFC 9110)** | 2 | 1 | 1 | 3 | 4 | 3 | 4 | 1 | **2.44** | STD 97, but narrative prose with no vectors and no page count obtainable. Not reifiable in the estate's sense |
| 33 | **Console** | 4 | 2 | 4 | 1 | 1 | 4 | 1 | 1 | **2.35** | ECMA-429 member, algorithmic, small — and almost no proof surface worth having |
| 34 | **multipart/form-data (RFC 7578)** | 1 | 2 | 4 | 1 | 3 | 3 | 4 | 1 | **2.29** | Prose only, no grammar, no algorithm, no vectors, governing a format Effect implements in `MultipartParser.ts`. High value, no normative anchor |
| 35 | **Cookies** | 4 | 1 | 3 | 1 | 3 | 1 | 4 | 1 | **2.19** | Algorithm-first in practice, and Effect has `Cookies.ts` — but there is no citable stable spec, which is disqualifying for a pinned model |
| 36 | **data URLs (RFC 2397)** | 2 | 1 | 5 | 1 | 2 | 3 | 2 | 1 | **2.08** | Five pages and three BNF productions, both of whose normative references are obsolete. Fetch re-specifies it anyway |
| 37 | **Media types (RFC 2045/6838)** | 2 | 1 | 4 | 2 | 2 | 2 | 3 | 1 | **2.06** | Superseded in practice by MIME Sniffing's parse and serialize algorithms |
| 38 | **HTTP Caching (RFC 9111)** | 3 | 1 | 3 | 1 | 4 | 1 | 2 | 1 | **2.03** | The age arithmetic is genuinely formalizable; nothing else here is |
| 39 | **Problem Details (RFC 9457)** | 2 | 1 | 5 | 1 | 2 | 1 | 3 | 1 | **1.86** | A JSON Schema in an appendix is not an algorithm |
| 40 | **HTTP/2 (RFC 9113)** | 3 | 1 | 1 | 1 | 2 | 1 | 1 | 1 | **1.45** | **Rejected.** Binary connection multiplexing with no JS-visible semantics to compile to |

Two caveats on this table, stated rather than hidden.

**A failed fetch affects rows 11 and 12.** The ECMAScript multipage
pages at https://tc39.es/ecma262/multipage/structured-data.html and
https://tc39.es/ecma262/multipage/control-abstraction-objects.html both returned
only the navigation table of contents, truncated before the clause body, on
three attempts with different anchors. What is verified is the size of
`spec.html`, 3,088,170 bytes, from
https://api.github.com/repos/tc39/ecma262/contents/. INFERRED, from memory: the
structured-data clause is 25, control abstraction objects is 27, and
`JSON.parse`/`JSON.stringify` are specified through numbered abstract operations
named `InternalizeJSONProperty` and `SerializeJSONProperty`. Anyone acting on
those rows should confirm the clause numbers by hand.

**The string hazard is structural and affects every row.** Lean's `String` holds
Unicode scalar values, which by definition exclude surrogates; JavaScript
strings are UTF-16 code unit sequences that may contain lone surrogates, and the
URL, Encoding, and Streams specifications all have observable behaviour on
exactly those inputs. No model in this survey may use Lean `String` as its
carrier. The carrier has to be a list of code units, or Infra's byte sequences
and code points, with conversions proved. This is a design constraint on the
whole programme, established from
https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/.

## 4. Dependency-ordered programs

Five programmes. The ordering inside each is forced by the dependency edges in
section 2.3; the ordering between them is a judgment.

### P1 — The substrate: Infra, then Web IDL's binding subset, then Encoding's UTF-8 core

Nothing else can be stated precisely until this exists. Infra supplies the byte
sequence, code point, list, map, and struct vocabulary that every other
specification's algorithms are written in, and it is 104 KB with no
dependencies. The Web IDL binding subset supplies the type conversions that every
IDL-defined operation performs at its boundary. Encoding's UTF-8 encoder and
decoder supply the one total function pair that every text-handling target needs.

What it unlocks: the vocabulary in which every later combinator is typed, and
the first genuine round-trip theorems — UTF-8 encode then decode is the identity
on scalar value sequences, and decode then encode is idempotent on byte
sequences modulo the replacement character. Those are the shape of every law the
later programmes want.

Main risk: scope creep into the legacy encodings. `index-gb18030.txt` alone is
843,967 bytes and `indexes.json` is 530,213 bytes. Model UTF-8, admit the legacy
tables as generated data with a seal, and refuse to prove anything about them
until someone asks.

### P2 — Identity: URL, on the substrate

The URL Standard is the highest-scoring single target in this survey and the
programme's first flagship. It is a named-state parser over a first-order state
record, which is exactly the shape this estate reifies well, and it comes with
228,685 bytes of `urltestdata.json` plus 82,134 bytes of setter tests as a
replayable corpus. UTS 46 enters as a profiled boundary, not a model: the
mapping table is a per-code-point Unicode database and modelling it is a
separate decision.

What it unlocks: `parse : List CodeUnit → Option Url` and
`serialize : Url → List CodeUnit` as total functions, with the idempotence and
round-trip theorems that make a verified URL utility library possible; the
`URLSearchParams` layer as a proved bidirectional codec; and a base-and-relative
resolution operation with an associativity story. This is the most direct route
from a Lean model to a shipped, provably-correct utility that a working web
developer would actually import.

Main risk: IDNA. If UTS 46 is pulled in rather than profiled out, the programme
absorbs a Unicode version dependency, and the tractability score of the UTS 46
row becomes the programme's score instead of the URL row's.

### P3 — Effects: Streams plus the promise job queue

These belong together and cannot be separated. This repository has already ruled
that the promise job queue is FIFO, deterministic, and therefore state inside
the configuration rather than a decision kind; that ruling is what makes
settlement-order theorems statable at all. Streams supplies the state machines;
the job queue supplies the ordering. Compression Streams and the Encoding
Standard's `TextEncoderStream`/`TextDecoderStream` are the first consumers, and
`AbortSignal` is the interruption boundary.

What it unlocks: this is the combinator programme. `pipeThrough`, `pipeTo`, and
`tee` become operations with proved laws under a named observation mask —
associativity of piping, the tee-then-merge relationship, backpressure
preservation under composition. That is the "algebraic and effectful combinators
that compile to JS/TS" the question asks for, and it maps onto Effect v4's
`Stream`, `Channel`, and `Sink` modules directly.

Main risk: the observation mask. Every one of those laws is true under M1 and
may be false under M2, because settlement order is observable. A law proved
without naming its mask is not a law.

### P4 — The server program: HTTP/1.1 message syntax, Structured Fields, multipart

The shape of a verified server-side toolkit. Structured Fields is the anchor,
because RFC 9651 is the one IETF document in this field whose algorithms bind
and whose grammar does not, and because 25 JSON test files exist to replay
against. HTTP/1.1 message framing supplies chunked decoding. Multipart supplies
body parsing.

What it unlocks: header parsing and serialization as a proved bidirectional
codec over a typed field algebra — items, lists, dictionaries, parameters — which
is the single most error-prone surface in every HTTP library; and message
framing theorems, which are the formal content of request smuggling.

Main risk: normative anchoring, and it is severe. RFC 9110 is narrative prose
with no vectors. RFC 7578 is prose with no grammar, no algorithm, and no
vectors, governing multipart. Cookies have no citable stable spec at all: draft
6265bis-22 expired 2026-06-04 and a layered-cookies draft already claims to
obsolete it. Structured Fields is anchorable; the rest of this programme needs a
decision about what it is even claiming conformance to.

### P5 — The data program: Base64, JSON, CBOR

The cheapest programme with the highest ratio of proof to effort, and the right
place to prove the estate's discipline transfers to a new domain. RFC 4648 is 18
pages with 21 vectors printed in the document. CBOR's Appendix B is a 256-row
jump table over every possible initial byte, which is a case analysis a Lean
model can mirror exactly. JSON adds the ECMAScript layer where reviver,
replacer, and property ordering live.

What it unlocks: total encoders and decoders with `decode ∘ encode = id`,
injectivity, and canonical-form theorems; and the negative results that matter
in practice — that WHATWG's forgiving base64 in Infra is *not* RFC 4648 base64,
and where the two disagree. Effect v4 already exposes exactly this surface in
`packages/effect/src/Encoding.ts`, so a checked lowering has an obvious target.

Main risk: low ambition. None of this touches the web platform's compatibility
surface except through `atob`/`btoa`, and CBOR has no platform surface at all.
This programme proves method; it does not by itself buy compatibility.

## 5. Prior art for the top candidates

The question behind this section is whether a target is already taken. The
answer, for almost all of the high-ranked ones, is no — and the reason is worth
stating plainly before the details.

### 5.0 The Lean 4 result

**There is essentially no Lean 4 formalization of any web standard.** The
complete inventory found:

| Project | Standard | Nature | Theorems? |
| --- | --- | --- | --- |
| SpecTec Lean 4 backend, Joachim Breitner, 2023 — https://github.com/Wasm-DSL/spectec/pull/2, branch `joachim`, confirmed via https://leanprover-community.github.io/archive/stream/113488-general/topic/WebAssembly.20spec.20in.20Lean4.html | WebAssembly | Lean 4 definitions generated from the SpecTec DSL; the first theorem-prover backend for SpecTec | **None.** Generated code on an unmerged branch |
| https://github.com/T-Brick/lean-wasm | WebAssembly | Hand-written executable model mirroring the official spec | **None.** Vector instructions, float execution, and module instantiation incomplete |
| https://github.com/predictable-machines/lean4-json-schema | JSON **Schema** | `JSONSchema` inductive, total `validateJson`, deriving handlers | Claims soundness and completeness; self-described as not covering the full standard, API unstable. Vendor library, not independently audited. The announcement blog returned HTTP 403 and was not fetched |
| https://github.com/algebraic-dev/http | HTTP | "HTTP primitives for Lean 4" | INFERRED: an ordinary library, no proofs |
| https://eprint.iacr.org/2024/1880 (Doussot, `gdncc/Cryptography`) | FIPS 202 | Pure Lean 4 SHA-3, passes NIST vectors | Implementation and vectors, **not** an `Impl = Spec` proof |
| https://arxiv.org/abs/2607.03406 (LeanDY, Jeanteur et al., July 2026) | Not a web standard | Dolev-Yao symbolic protocol verification framework in Lean 4 | Yes — but the case study is blockchain payment channels |

Meanwhile Coq has WasmCert, JSCert, Warblre, Narcissus, WebSpec, and Quark;
Isabelle has WasmCert and the AFP Core DOM family; F* has EverParse and EverCBOR;
K has KJS; ProVerif has Cookie Crumbles; Dafny has base64. Lean 4 has two
theorem-free WebAssembly models and a vendor JSON Schema library.

LeanDY is the interesting datum: the protocol-verification *tooling* now exists
in Lean 4, and the web standards to point it at do not.

### 5.1 Per-target prior art

**Infra.** No formalization found. Not separately searched as a named target;
recorded as not established rather than as a confirmed absence.

**URL (and RFC 3986).** **No verified URL parser in any prover.** What exists is
empirical and non-formal: "Exploiting URL Parsing Confusion" (Claroty Team82 and
Snyk, 2022, https://claroty.com/team82/research/exploiting-url-parsing-confusion)
documents five inconsistency classes across 16 libraries, and "Equivocal URLs"
(ESORICS 2022, https://dl.acm.org/doi/10.1007/978-3-031-17143-7_9) measures
parser divergence. Ada URL (https://arxiv.org/abs/2311.10533) is
WHATWG-conformant and conformance-tested, not verified. The Web Infrastructure
Model treats URLs as abstract structured terms, so origin comparison is modelled
at the protocol level while character-level parsing is not. This is the sharpest
negative space in the survey: a documented attack class that is definitionally a
spec-conformance problem, with no mechanized specification anywhere.

**Encoding / UTF-8.** **No Coq, Isabelle, or F\* verified UTF-8 codec found**
across four differently-phrased searches plus an AFP-restricted search. Coq's
`Coq.Unicode.Utf8` is notation, not a formalization. The nearest active work is
`model-checking/verify-rust-std`
(https://raw.githubusercontent.com/model-checking/verify-rust-std/main/doc/src/SUMMARY.md),
whose open challenges 10, 13, and 20–22 target `String`, `CStr`, and `str`
patterns — but those are **memory-safety and UB-freedom obligations, not
functional correctness**. Nobody is proving `decode ∘ encode = id` or that
`from_utf8` accepts exactly the well-formed sequences of Unicode Table 3-7.

**Streams.** **No formalization of the WHATWG Streams Standard in any prover.**
Two independent searches returned only the spec text. Adjacent work exists on
stream semantics generally — Kahn process networks in Coq (Paulin-Mohring, 2007,
https://www.lri.fr/~paulin/PUBLIS/paulin07kahn.pdf), stream components in
Isabelle/HOL (https://arxiv.org/abs/1405.1512), and Interaction Trees as the
plausible substrate — but backpressure specifically, the coupling of a consumer's
`desiredSize` to producer pull, appears nowhere. This repository's target is
unclaimed.

**Promise jobs and the event loop.** **No mechanization found.** λ_p (Madsen,
Lhoták, Tip, OOPSLA 2017, https://cs.au.dk/~magnusm/papers/oopsla17/paper.pdf) is
a paper calculus for a subset of ES6 promises; INFERRED that no Coq or Isabelle
artifact accompanies it. "Semantics of Asynchronous JavaScript"
(https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/asyncNodeSemantics.pdf)
gives a Node event-loop operational semantics on paper. ECMAScript itself is
heavily formalized — JSCert in Coq (https://www.doc.ic.ac.uk/~pg/publications/Bodin2014Trusted.pdf),
KJS in K (https://fsl.cs.illinois.edu/publications/park-stefanescu-rosu-2015-pldi.pdf),
Warblre for regex matching in Coq (https://arxiv.org/abs/2403.11919), and ESMeta
(https://github.com/es-meta/esmeta), which extracts a mechanized executable spec
from ECMA-262 itself but proves nothing. Crucially the **microtask checkpoint
lives in the HTML spec, not ECMA-262**, so the ECMAScript-to-HTML job-queue seam
is modelled by nobody.

**Base64 (RFC 4648).** **One hit, in Dafny, not an ITP**: the `dafny-lang/libraries`
`Base64` module (https://github.com/dafny-lang/libraries/pull/3/files) carries a
full round-trip postcondition `ensures Decode(s) == Success(b)`, mutually-inverse
block lemmas, and separate verified padding paths. No Coq, Isabelle, F\*, Agda,
ACL2, or Lean base64 found. Not covered anywhere: **base64url** (RFC 4648 §5, the
JOSE alphabet), MIME line wrapping, and canonical-form non-malleability —
rejecting non-zero padding bits — which are exactly the properties JWT security
depends on.

**Structured Fields (RFC 9651).** Not separately searched in this pass. Recorded
as **not established**; treat the absence as unverified rather than as evidence.

**Web IDL.** Not separately searched in this pass. Same caveat.

**HTTP/1.1 message framing.** Partial prior art, and not where one would expect
it. **EverParse does not cover HTTP** — it targets binary, length-prefixed
formats: TLS, PKCS, CBOR (https://project-everest.github.io/assets/everparse.pdf).
The real work is Coq and Interaction Trees: "From C to Interaction Trees" (Koh
et al., CPP 2019, https://arxiv.org/abs/1811.11911) verified a networked server
against an ITree spec for **a fragment of HTTP/1.1**, and derived a tester that
caught RFC violations in Apache and nginx; `coq-http`
(https://github.com/liyishuai/coq-http) continues it. Coverage is a fragment
sufficient for a key-value server, not RFC 9110 or 9112 framing. **Request
smuggling has no formalization at all** — T-Reqs (CCS 2021) and HTTP Garden
(https://arxiv.org/pdf/2405.17737) are differential fuzzing, and the HTTP Garden
paper explicitly names "a formally-verified parser" as the unmet ideal.

**JSON and CBOR.** Asymmetric. **CBOR is strongly covered**: EverCBOR / EverCDDL
/ EverCOSE (Ramananandro, Ebner, Martínez, Swamy, MSR, May 2025,
https://arxiv.org/html/2505.17335v1) give verified C and Rust parsers and
serializers in F\* with separation logic, including a proof that deterministic
CBOR is **non-malleable**, plus the first formalization of CDDL. **JSON is not**:
`Nano_JSON` in the AFP (https://isa-afp.org/entries/Nano_JSON.html) is a utility
entry, and JSON otherwise appears only as the worked example of general verified
parser generators — the AFP LL(1) generator
(https://www.isa-afp.org/entries/LL1_Parser.html), Vermillion in Coq
(https://tupl.cs.tufts.edu/papers/itp2019_ll1.pdf), and Coqlex. No verified JSON
parser with an RFC 8259 round-trip theorem was found. Narcissus (ICFP 2019,
https://arxiv.org/abs/1803.04870) is the closest general framework for
correct-by-construction codecs with proven inverse properties, applied to binary
packet formats rather than text.

**Web platform models generally, and one correction.** The task brief described
the Web Infrastructure Model as "in Isabelle by Fett/Küsters/Schmitz". **That is
not supported.** WIM (https://www.sec.uni-stuttgart.de/research/wim/,
https://arxiv.org/abs/1403.1866) is a hand-written Dolev-Yao-style mathematical
model with hand proofs, applied to BrowserID, OAuth 2.0, OpenID Connect (CSF
2017), FAPI, and GNAP; no Isabelle mechanization of it was found. The mechanized
browser models are elsewhere: **WebSpec** (Veronese, Farinier, Tempesta,
Squarcina, Maffei, IEEE S&P 2023, https://arxiv.org/abs/2201.01649) in Coq plus
Z3, with ten formalized web-security invariants and executable attack traces;
**Quark** (Jang, Tatlock, Lerner, USENIX Security 2012,
https://goto.ucsd.edu/quark/) in Coq, proving tab non-interference and cookie
integrity over a small verified kernel; and Brucker and Herzberg's Isabelle/HOL
**Core DOM** family in the AFP (https://www.isa-afp.org/entries/Core_DOM.html,
https://www.isa-afp.org/entries/Shadow_DOM.html), which covers the node tree and
its invariants but not events, ranges, mutation observers, or HTML parsing.

**Cookies.** The protocol is modelled; the algorithm is not. Cookie Crumbles
(Squarcina, Adão, Veronese, Maffei, USENIX Security 2023,
https://www.usenix.org/system/files/usenixsecurity23-squarcina.pdf) gives a
ProVerif model of cookie-based session integrity and found flaws in 9 of the top
13 web frameworks. No mechanization of RFC 6265bis **as a parsing specification**
— the cookie-string algorithm, attribute parsing, prefix rules, store ordering —
was found.

**JOSE / JWT.** **No formalization found at either level.** No Tamarin, ProVerif,
or ITP model of JWS, JWE, or JWK surfaced; algorithm confusion (`alg: none`,
RS256 to HS256) is documented only in practitioner literature. WIM's OpenID
Connect analysis models ID tokens as abstract signed terms, which abstracts away
the JOSE header, `alg` negotiation, key selection, and base64url encoding —
precisely where the real attacks live. EverCOSE is the structurally analogous
artifact in the CBOR world; JOSE has no counterpart.

## 6. Recommendation

### Target 0, unavoidable: Infra

Not a headline deliverable and not counted in the five below, because it ships no
user-visible utility. It is 104 KB, has no dependencies, and every other
candidate's algorithms are written in its vocabulary. Nothing else in this survey
can be stated precisely until it exists. Do it first and do not scope it larger
than the byte sequence, code point, list, map, struct, JSON, and forgiving base64
sections.

### The top five

1. **WHATWG URL** — the highest weighted total in the survey (4.53), a
   named-state parser that is exactly the shape this estate reifies well, 228,685
   bytes of `urltestdata.json` to replay against, an ECMA-429 member, and no
   verified URL parser exists in any prover despite a documented attack class.
2. **WHATWG Encoding, UTF-8 core only** (4.49) — decoder and encoder state
   machines, 340 WPT files, direct reuse of fips202's byte and bit machinery, and
   no functional-correctness UTF-8 codec exists in any ITP.
3. **WHATWG Streams together with the promise job queue** (4.25 and 4.05) — the
   combinator prize: `pipeThrough`, `pipeTo`, and `tee` as operations with proved
   laws under a named mask, matching Effect v4's `Stream`, `Channel`, and `Sink`,
   with zero prior art on backpressure in any system.
4. **RFC 9651 Structured Field Values** (3.63) — the only IETF spec in this field
   whose algorithms bind and whose ABNF is explicitly informative, with 25 JSON
   test files in a public external suite, anchoring an otherwise unanchorable
   server-side programme.
5. **RFC 4648 Base64** (4.10) — 18 pages, 21 vectors printed in the document,
   `Effect.Encoding` already exposing the exact surface, and the only prior art
   is Dafny and covers neither base64url nor non-malleability.

### Recommended order

Infra → Encoding (UTF-8 core) → URL → Base64 → Streams with the promise job
queue → Structured Fields → Fetch as the long-run integrator.

Base64 sits fourth deliberately. It is the cheapest complete target in the
survey and the right place to demonstrate that the fips202 `Impl = Spec`
discipline transfers to a non-cryptographic standard, before committing to
Streams. It can also run in parallel with URL, since after Infra the two share
nothing.

Fetch is the destination, not a step. It scores 3.87 on the strength of
expressivity and compatibility alone while being 444 KB with ten normative
dependencies — nine of which are the first six items in this order. It becomes
tractable only after they land, and attempting it earlier means modelling all of
them badly at once.

### What each contributes to the two repositories

| Target | To `lean4-WHATWG-streams` | To `lean4-effect4` |
| --- | --- | --- |
| **Infra** | The vocabulary the Streams algorithms are already written in — byte sequences, lists, structs — replacing ad-hoc carriers before any semantic declaration exists | A first-order data substrate for `Flow` payloads that is neither Lean `String` nor a host closure |
| **Encoding** | `TextEncoderStream` and `TextDecoderStream` are Streams consumers; a proved UTF-8 codec makes the first end-to-end transform chain statable | A checked lowering target with round-trip laws, and the resolution of the UTF-16-versus-scalar-value carrier question for every generated string |
| **URL** | Little directly; it is the parallel flagship that proves the method on a second standard | A verified utility library that compiles to JS/TS and that a working developer would import — the clearest demonstration of "universal properties to DX" |
| **Base64** | Reuse of the fips202 discipline on the digests and vendor seals the gates already depend on | A direct match for `packages/effect/src/Encoding.ts`, with the negative result that WHATWG forgiving base64 is not RFC 4648 base64 |
| **Streams + jobs** | This *is* the repository's target; the job-queue half is already ruled as configuration state rather than a decision kind under DB-03, and the piping requirements are already the P7 flagship under DB-05 | The concrete instance the relational semantics and observation masks were designed for, and the bridge to Effect v4's `Stream`, `Channel`, and `Sink` |
| **Structured Fields** | Nothing directly | A typed field algebra under `effect/unstable/http/Headers.ts`, and the anchor for a server-side programme whose other members have no citable spec |

### Three findings that should change how the estate cites things

- **Effect v4 moved the HTTP stack.** As of `Effect-TS/effect` commit
  `829aff97d71d7900b7765ba2f63e33874b898cdc` (fetched 2026-09-02),
  `packages/platform/` has no `src` at all; `HttpClient`, `HttpServer`,
  `HttpApi`, `Url`, `UrlParams`, `Headers`, `Cookies`, `Socket`, and `Multipart`
  live under `packages/effect/src/unstable/`. `MsgPack` was removed in favour of
  `SchemaBinary`. Any estate text saying the HTTP stack is in `@effect/platform`
  is now wrong for v4.
- **WinterCG is Ecma TC55, and the API list is a published standard.** Cite
  **ECMA-429, "Minimum common web API", 1st edition, December 2025**
  (https://ecma-international.org/publications-and-standards/standards/ecma-429/),
  not a community-group draft. The `min-common-api.proposal.wintercg.org` host is
  dead; the live editor's draft is at `min-common-api.proposal.wintertc.org`.
  **WebSocket is not in it**, despite Node, Bun, Deno, and Workers all shipping
  it — it is de facto, not de jure.
- **Cookies cannot be pinned.** draft-ietf-httpbis-rfc6265bis-22 (2025-12-01)
  expired 2026-06-04 with no RFC number, and
  draft-ietf-httpbis-layered-cookies-02 (2026-05-21) declares it obsoletes "RFC
  6265 and 6265bis". Cite RFC 6265 or a dated draft revision; never "6265bis"
  bare.

## 7. What could not be verified

- **The ECMAScript clause bodies.** Three fetches of
  https://tc39.es/ecma262/multipage/structured-data.html and
  https://tc39.es/ecma262/multipage/control-abstraction-objects.html, with and
  without anchors, returned only the truncated navigation table of contents. The
  clause numbers for structured data (25) and control abstraction objects (27),
  and the abstract-operation names `InternalizeJSONProperty` and
  `SerializeJSONProperty`, are INFERRED from memory. Only the size of
  `spec.html`, 3,088,170 bytes, is fetched fact.
- **Page counts for RFC 6455** (three fetches returned 39, 73, and 98) and **RFC
  7515** (47 versus 58). Both unresolved; do not cite either without a manual
  check. Page counts for RFC 9110, 9111, 9112, 9651, 8949, and 9457 were not
  surfaced by any fetch.
- **Maturity levels for RFC 2045, 2046, 7578, and 2397** came only from the
  in-document "Standards Track" category line, not the `/info/` maturity field.
  Proposed versus Draft Standard is unconfirmed for those four.
- **Updated-by lists for RFC 2045 and 2046** are INFERRED. Separately, the plain
  rfc-editor HTML rendering proved unreliable for "updated by" — it reported none
  for both RFC 7519 and RFC 6455, while the `/info/` pages listed RFC 7797 and
  8725 for the former and RFC 7936, 8307, and 8441 for the latter. Use `/info/`.
- **Prior art for Structured Fields and Web IDL** was not separately searched.
  Their absence from section 5 is unverified, not established.
- **The `lean4-json-schema` proof claims** were not audited; its announcement
  blog returned HTTP 403 and was not fetched.
- **Deno's web-platform-APIs page is not exhaustive**, so support for Streams,
  URL, TextEncoder, and Headers in Deno is not asserted from a fetched source
  here even though those APIs exist.
- **The estate's own fips202 artifact** was read locally at
  `C:\Users\kokok\Dev\foldlab\formal\fips202\README.md` and not re-verified by
  running its gates in this session.

