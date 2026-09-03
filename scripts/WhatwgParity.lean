import Lean
import Whatwg
import WhatwgTest

/-!
# Rename parity receipt (WP-7)

One row per constant compiled from every module under the production root
and the test root: name, module, kind, universe parameters, `pp.all` type,
`pp.all` value (definitions only), and axiom set. The test-root prefix is
normalised to `«TEST»` and the production prefix to `«ROOT»`, in the four
spellings a prefix takes (name prefix, string literal, underscore-joined
auxiliary name, and a gate message prefix followed by a space). The check
script additionally normalises hygiene context numbers inside universe-level
names, which derive from the module name, and collapses runs of spaces,
because the pretty-printer wraps at a fixed width and a prefix of a different
length moves the wrap points without changing a token. Run before and after the rename; the outputs must be
byte-identical. Usage: `PARITY_OUT=<file> lake env lean scripts/WhatwgParity.lean`.
-/

open Lean Meta Elab

namespace WhatwgParity

/-- Prefix tables for the two sides of the W2 rename, longest first so a
longer prefix is rewritten before a prefix it starts with. `PARITY_SIDE=before`
selects the pre-rename spellings (the imports above must then be the old
roots; the committed source receipt was taken that way at `f5dbad8`). -/
def prefixesBefore : List (String × String) :=
  [ ("WhatwgStreamsTest", "«TEST»"), ("WhatwgStreams", "«ROOT»") ]

def prefixesAfter : List (String × String) :=
  [ ("WhatwgTest.Streams", "«TEST»"), ("WhatwgTest/Streams", "«TEST»")
  , ("WhatwgTest", "«TEST»"), ("Whatwg.Streams", "«ROOT»"), ("Whatwg/Streams", "«ROOT»")
  , ("Whatwg", "«ROOT»") ]

def normalise (prefixes : List (String × String)) (s : String) : String :=
  let s := prefixes.foldl (fun acc (p, r) =>
    ((acc.replace (p ++ ".") (r ++ "."))
      |>.replace ("\"" ++ p ++ "\"") ("\"" ++ r ++ "\"")
      |>.replace ("_" ++ p ++ "_") ("_" ++ r ++ "_")
      |>.replace (p ++ " ") (r ++ " "))) s
  s.replace "\n" " "

/-- The gate module is tooling whose message strings name the tree; it is
excluded from the receipt on both sides. -/
def audited (side : String) (modName : Name) : Bool :=
  let roots : List Name := if side == "before" then [`WhatwgStreams, `WhatwgStreamsTest] else [`Whatwg, `WhatwgTest]
  roots.any (·.isPrefixOf modName) && !(modName.toString.endsWith "Audit.AxiomGate")
    -- Libraries added after the W2 rename are outside the receipt's scope:
    -- the receipt proves the rename changed nothing, and `Whatwg.Html`
    -- (H2 of docs/HTML-PACKAGE-PLAN.md) did not exist at `f5dbad8`.
    && !(`Whatwg.Html).isPrefixOf modName && !(`WhatwgTest.Html).isPrefixOf modName

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

def ppAll (prefixes : List (String × String)) (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.all true) (ppExpr e)
  return normalise prefixes (toString fmt)

run_elab do
  let env ← getEnv
  let some out ← liftM (IO.getEnv "PARITY_OUT") | throwError "PARITY_OUT is unset"
  let side := (← liftM (IO.getEnv "PARITY_SIDE")).getD "after"
  let prefixes := if side == "before" then prefixesBefore else prefixesAfter
  let mut rows : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    unless audited side modName do continue
    let ty ← ppAll prefixes info.type
    let value ← match info with
      | .defnInfo d => ppAll prefixes d.value
      | _ => pure ""
    let axioms ← collectAxioms name
    let axiomNames := (axioms.map toString).qsort (· < ·)
    let levels := normalise prefixes (String.intercalate "," (info.levelParams.map toString))
    rows := rows.push <| String.intercalate "\t"
      [ normalise prefixes name.toString, normalise prefixes modName.toString, kindOf info, levels
      , ty, value, String.intercalate "," axiomNames.toList ]
  let sorted := rows.qsort (· < ·)
  liftM <| IO.FS.writeFile out (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"whatwg parity: {sorted.size} constants written to {out}"

end WhatwgParity
