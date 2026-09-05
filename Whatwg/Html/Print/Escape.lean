/-!
# Whatwg.Html.Print.Escape

Character escaping for the serializer, ported from TyXML's `xml_print.ml`:
`is_control`, `add_unsafe_char`, `encode_unsafe_char` and
`encode_unsafe_char_and_at`. Slice H4 of `docs/HTML-PACKAGE-PLAN.md`.

Everything is defined at `List Char` and lifted to `String` by
`String.ofList` at one boundary, so every statement below is a `List` fact
that `String.toList_ofList` transports. Nothing here reads or writes a
`String` index.

## What is escaped

`add_unsafe_char` replaces `<`, `>`, `"` and `&` by their named references
and every character TyXML's `is_control` names (code `≤ 8`, `= 11`, `= 12`,
`14`–`31`, `= 127`) by a decimal numeric reference `&#N;`. Tab, line feed and
carriage return are *not* control characters by that predicate, and so pass
through unescaped; that is TyXML's rule, reproduced here.

## What the theorems say

- `escape_no_delim`: no character that could end a text run or an attribute
  value — `<`, `>`, `"` — survives escaping, for any input whatsoever.
- `escape_no_control`: no control character survives escaping.
- `unescape_escape`: the local decoder `unescape` recovers the input from the
  escaped form, for every input. This is the honest form of "no unescaped
  `&`": `escape_no_delim` cannot be stated for `&`, since `&` begins every
  reference the escaper emits, and Lean refutes the statement that it can.
- `escape_injective`: two inputs with the same escaping are equal, a
  corollary of the round trip.

`unescape` is a decoder for one alphabet — the four named references and the
at most three-digit numeric references `escape` itself emits — and not an
HTML parser. It does not tokenize markup, it knows nothing of tags,
attributes or the named-character-reference table, and it is deliberately
unspecified on input outside that alphabet. Ruling HP-8 of
`docs/HTML-PACKAGE-PLAN.md` refuses a parse round trip until a parser exists,
and nothing here is one.
-/

namespace Whatwg.Html.Print

/-! ## The escaper -/

/-- TyXML's `is_control`: code point `≤ 8`, `= 11`, `= 12`, in `14`–`31`, or
`= 127`. Tab (`9`), line feed (`10`) and carriage return (`13`) are excluded,
so they are emitted literally. -/
def isControl (c : Char) : Bool :=
  c.toNat ≤ 8 || c.toNat == 11 || c.toNat == 12
    || (14 ≤ c.toNat && c.toNat ≤ 31) || c.toNat == 127

/-- The characters whose appearance in a text run or an attribute value would
change where that run ends. `&` is deliberately absent: it begins every
reference the escaper emits, so no output is free of it, and the statement
that it is would be false. -/
def isDelim (c : Char) : Bool := c == '<' || c == '>' || c == '"'

/-- A decimal numeric character reference, `&#N;`, with the digits of `N` in
base ten. TyXML writes `"&#" ^ string_of_int (Char.code c) ^ ";"`. -/
def numericRef (n : Nat) : List Char := '&' :: '#' :: (Nat.toDigits 10 n ++ [';'])

/-- TyXML's `add_unsafe_char`, as a function into the characters it would
have appended to the buffer: the four named references, a decimal numeric
reference for a control character, and the character itself otherwise. The
`if` chain rather than a literal-pattern `match` is deliberate: `split`
produces usable disequality hypotheses from it. -/
def escapeChar (c : Char) : List Char :=
  if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if isControl c then numericRef c.toNat
  else [c]

/-- TyXML's `encode_unsafe_char`, at `List Char`. -/
def escape (l : List Char) : List Char := l.flatMap escapeChar

/-- The extra case of TyXML's `encode_unsafe_char_and_at`: `@` becomes
`&#64;`, everything else is `escapeChar`. -/
def escapeCharAndAt (c : Char) : List Char :=
  if c = '@' then ['&', '#', '6', '4', ';'] else escapeChar c

/-- TyXML's `encode_unsafe_char_and_at`, at `List Char`. -/
def escapeAndAt (l : List Char) : List Char := l.flatMap escapeCharAndAt

/-- The public escaper. `String.ofList` is the only `String` operation in
this module. -/
def escapeString (s : String) : String := String.ofList (escape s.toList)

/-- The public escaper of `encode_unsafe_char_and_at`. -/
def escapeAndAtString (s : String) : String := String.ofList (escapeAndAt s.toList)

/-! ## Facts about the digits of a small number

Every numeric reference the escaper emits is the reference of a control
character, whose code is below `128`. The three facts the proofs below need
about such a number's decimal digits are decided by evaluation over those
`128` cases at once. -/

/-- The value of a list of decimal digit characters, most significant
first. -/
def natOfDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- A digit character, and not any of the characters the decoder or the
soundness statements below give a meaning to. -/
def digitOk (c : Char) : Bool :=
  c.isDigit && !isControl c && !isDelim c && c != '&' && c != '#' && c != ';'

/-- The digits of a number below `128`: they read back as that number, there
are one to three of them, and each is an ordinary decimal digit. Decided by
evaluation over the `128` cases. -/
theorem toDigits_facts : ∀ n, n < 128 →
    natOfDigits (Nat.toDigits 10 n) = n
      ∧ 1 ≤ (Nat.toDigits 10 n).length
      ∧ (Nat.toDigits 10 n).length ≤ 3
      ∧ (Nat.toDigits 10 n).all digitOk = true := by decide

/-- The three consequences of `digitOk` the decoder proofs use: the character
is a decimal digit, and it is neither `;` nor `&`. -/
theorem digitOk_facts {c : Char} (h : digitOk c = true) :
    c.isDigit = true ∧ c ≠ ';' ∧ c ≠ '&' := by
  simp only [digitOk, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1.1.1.1, h.2, h.1.1.2⟩

/-- A control character's code is below `128`. -/
theorem toNat_lt_of_isControl {c : Char} (h : isControl c = true) : c.toNat < 128 := by
  simp only [isControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  omega

/-! ## Soundness: the delimiters and the control characters are gone -/

/-- No delimiter is produced for any single character. -/
theorem escapeChar_no_delim (c d : Char) (hd : isDelim d = true) : d ∉ escapeChar c := by
  simp only [isDelim, Bool.or_eq_true, beq_iff_eq] at hd
  unfold escapeChar
  split
  · rcases hd with (rfl | rfl) | rfl <;> decide
  split
  · rcases hd with (rfl | rfl) | rfl <;> decide
  split
  · rcases hd with (rfl | rfl) | rfl <;> decide
  split
  · rcases hd with (rfl | rfl) | rfl <;> decide
  split
  · rename_i hc
    simp only [numericRef, List.mem_cons, not_or]
    refine ⟨?_, ?_, ?_⟩
    · rcases hd with (rfl | rfl) | rfl <;> decide
    · rcases hd with (rfl | rfl) | rfl <;> decide
    · intro hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      have hlt := toNat_lt_of_isControl hc
      have hall := (toDigits_facts c.toNat hlt).2.2.2
      rw [List.all_eq_true] at hall
      cases hmem with
      | inl hin =>
          have := hall d hin
          simp only [digitOk, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at this
          rcases hd with (rfl | rfl) | rfl
          · exact absurd this.1.1.1.2 (by decide)
          · exact absurd this.1.1.1.2 (by decide)
          · exact absurd this.1.1.1.2 (by decide)
      | inr hin =>
          rcases hd with (rfl | rfl) | rfl <;> exact absurd hin (by decide)
  · rename_i h1 h2 h3 _ _
    simp only [List.mem_singleton]
    rcases hd with (rfl | rfl) | rfl
    exact Ne.symm h1
    exact Ne.symm h2
    exact Ne.symm h3

/-- No delimiter survives escaping, for any input. -/
theorem escape_no_delim (l : List Char) (d : Char) (hd : isDelim d = true) : d ∉ escape l := by
  induction l with
  | nil => simp [escape]
  | cons c cs ih =>
    simp only [escape, List.flatMap_cons, List.mem_append, not_or]
    exact ⟨escapeChar_no_delim c d hd, ih⟩

/-- No control character survives escaping: the escaper replaces each one by
its numeric reference, and the references are built from `&`, `#`, `;` and
decimal digits. -/
theorem escapeChar_no_control (c d : Char) (hd : d ∈ escapeChar c) : isControl d = false := by
  revert hd
  unfold escapeChar
  split
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> decide
  split
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> decide
  split
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  split
  · intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
  split
  · rename_i hc
    intro hd
    simp only [numericRef, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hd
    have hlt := toNat_lt_of_isControl hc
    have hall := (toDigits_facts c.toNat hlt).2.2.2
    rw [List.all_eq_true] at hall
    rcases hd with rfl | rfl | (hin | rfl)
    · decide
    · decide
    · have hok := hall d hin
      simp only [digitOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1.2
    · decide
  · rename_i _ _ _ _ h5
    intro hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    simpa using h5

/-- No control character survives escaping, for any input. -/
theorem escape_no_control (l : List Char) (d : Char) (hd : d ∈ escape l) :
    isControl d = false := by
  induction l with
  | nil => simp [escape] at hd
  | cons c cs ih =>
    simp only [escape, List.flatMap_cons, List.mem_append] at hd
    cases hd with
    | inl h => exact escapeChar_no_control c d h
    | inr h => exact ih h

/-! ## The decoder

`unescape` reads back exactly the alphabet `escape` writes: the four named
references and a numeric reference of at most three digits, which is all a
control character's code (below `128`) can need. It is not an HTML parser
(ruling HP-8): outside that alphabet its behaviour is arbitrary and no
theorem below says anything about it. -/

/-- The decoder for the escaper's own alphabet. Structural in its argument:
every recursive call is on a proper tail. -/
def unescape : List Char → List Char
  | [] => []
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescape rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescape rest
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescape rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescape rest
  | '&' :: '#' :: d₁ :: ';' :: rest =>
      if d₁.isDigit then Char.ofNat (natOfDigits [d₁]) :: unescape rest
      else '&' :: '#' :: d₁ :: ';' :: unescape rest
  | '&' :: '#' :: d₁ :: d₂ :: ';' :: rest =>
      if d₁.isDigit && d₂.isDigit then Char.ofNat (natOfDigits [d₁, d₂]) :: unescape rest
      else '&' :: '#' :: d₁ :: d₂ :: ';' :: unescape rest
  | '&' :: '#' :: d₁ :: d₂ :: d₃ :: ';' :: rest =>
      if d₁.isDigit && d₂.isDigit && d₃.isDigit then
        Char.ofNat (natOfDigits [d₁, d₂, d₃]) :: unescape rest
      else '&' :: '#' :: d₁ :: d₂ :: d₃ :: ';' :: unescape rest
  | c :: rest => c :: unescape rest

/-- Outside a reference, the decoder copies a character and recurses on the
tail. Every case of the decoder that does otherwise begins with `&`. -/
theorem unescape_cons_of_ne_amp {c : Char} (h : c ≠ '&') (t : List Char) :
    unescape (c :: t) = c :: unescape t := by
  rw [unescape]
  all_goals (intros; simp_all)

/-- The decoder reads back a numeric reference of a code below `128`, which
is every numeric reference the escaper emits. -/
theorem unescape_numericRef {n : Nat} (hn : n < 128) (rest : List Char) :
    unescape (numericRef n ++ rest) = Char.ofNat n :: unescape rest := by
  obtain ⟨hval, hlen1, hlen3, hall⟩ := toDigits_facts n hn
  rw [List.all_eq_true] at hall
  simp only [numericRef, List.cons_append, List.append_assoc, List.nil_append]
  generalize hds : Nat.toDigits 10 n = ds at hval hlen1 hlen3 hall
  clear hds
  match ds, hval, hlen1, hlen3, hall with
  | [], _, hlen1, _, _ => simp at hlen1
  | [d₁], hval, _, _, hall =>
      have h₁ := digitOk_facts (hall d₁ (by simp))
      simp only [List.cons_append, List.nil_append]
      rw [unescape.eq_6, if_pos h₁.1, hval]
  | [d₁, d₂], hval, _, _, hall =>
      have h₁ := digitOk_facts (hall d₁ (by simp))
      have h₂ := digitOk_facts (hall d₂ (by simp))
      simp only [List.cons_append, List.nil_append]
      rw [unescape.eq_7 d₁ d₂ rest h₂.2.1,
        if_pos (by simp [h₁.1, h₂.1]), hval]
  | [d₁, d₂, d₃], hval, _, _, hall =>
      have h₁ := digitOk_facts (hall d₁ (by simp))
      have h₂ := digitOk_facts (hall d₂ (by simp))
      have h₃ := digitOk_facts (hall d₃ (by simp))
      simp only [List.cons_append, List.nil_append]
      rw [unescape.eq_8 d₁ d₂ d₃ rest h₂.2.1 h₃.2.1,
        if_pos (by simp [h₁.1, h₂.1, h₃.1]), hval]
  | d₁ :: d₂ :: d₃ :: d₄ :: t, _, _, hlen3, _ => simp at hlen3

/-- The decoder recovers the character the escaper replaced, whatever
follows. -/
theorem unescape_escapeChar (c : Char) (rest : List Char) :
    unescape (escapeChar c ++ rest) = c :: unescape rest := by
  unfold escapeChar
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i hc
    rw [unescape_numericRef (toNat_lt_of_isControl hc) rest, Char.ofNat_toNat]
  · rename_i _ _ _ h4 _
    simpa using unescape_cons_of_ne_amp h4 rest

/-- The escaper's output decodes back to its input, for every input. This is
the statement that stands in for "no unescaped `&`": every `&` in the output
begins a reference, because the output decodes. -/
theorem unescape_escape (l : List Char) : unescape (escape l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escape, List.flatMap_cons] at *
    rw [unescape_escapeChar, ih]

/-- Escaping is injective, a corollary of the round trip. -/
theorem escape_injective {l₁ l₂ : List Char} (h : escape l₁ = escape l₂) : l₁ = l₂ := by
  have hd := congrArg unescape h
  rwa [unescape_escape, unescape_escape] at hd

/-- The `@` case of `encode_unsafe_char_and_at` decodes too: `&#64;` is the
numeric reference of `@`. -/
theorem unescape_escapeCharAndAt (c : Char) (rest : List Char) :
    unescape (escapeCharAndAt c ++ rest) = c :: unescape rest := by
  unfold escapeCharAndAt
  split
  · rename_i h
    subst h
    simp only [List.cons_append, List.nil_append]
    rw [unescape.eq_7 '6' '4' rest (by decide), if_pos (by decide)]
    rfl
  · exact unescape_escapeChar c rest

/-- The `and_at` escaper decodes back to its input as well. -/
theorem unescape_escapeAndAt (l : List Char) : unescape (escapeAndAt l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escapeAndAt, List.flatMap_cons] at *
    rw [unescape_escapeCharAndAt, ih]

/-! ## The `String` boundary -/

/-- The public escaper is the `List Char` escaper, transported by
`String.toList_ofList`. Every theorem above is a theorem about
`escapeString` through this equation. -/
theorem toList_escapeString (s : String) : (escapeString s).toList = escape s.toList := by
  simp [escapeString]

/-- The same, for the `and_at` escaper. -/
theorem toList_escapeAndAtString (s : String) :
    (escapeAndAtString s).toList = escapeAndAt s.toList := by
  simp [escapeAndAtString]

/-- Escaping a string is injective. -/
theorem escapeString_injective {s t : String} (h : escapeString s = escapeString t) : s = t := by
  apply String.toList_injective
  exact escape_injective (by rw [← toList_escapeString, ← toList_escapeString, h])

end Whatwg.Html.Print
