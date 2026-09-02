import Sha256.Api

/-!
# `Sha256.Context` — incremental SHA-256

`docs/SHA256-DAG.md` §4 A1.S5. A `Context` is the chaining state after every
complete 64-byte block absorbed so far, the pending partial block, and the
number of blocks already folded into the state. `update` absorbs whole blocks
out of `buffer ++ chunk` and keeps the tail; `finalize` pads the tail with the
total byte count and finishes.

The context carries no unbounded data: `buffer_lt` bounds the pending block by
64 bytes, and the bytes fed so far are not stored. What they were is expressed
by the relation `Absorbs`, and `finalize_absorbs` is the theorem that ties the
incremental result back to `Sha256.Impl.sha256` of exactly those bytes — which
`Sha256.Bridge.sha256_bridge` in turn ties to FIPS 180-4.

**Credit.** The shape — a state paired with a bounded buffer, the result
carrying its own size bound, and the append law as the central lemma — is
`Crypto.Hash.Internal.updateBuffered` and `updateBuffered_append` of
kim-em/lean-crypto-hash at commit
`54e6068abd4658fd91203cae1c2316188ffa0e89` (Apache-2.0), read first-hand and
recorded in `docs/SHA256-DAG.md` §3.5. No code is imported and the proof is not
theirs: their `updateBuffered` absorbs one byte at a time through
`ByteArray.data.foldl`, which makes their append law `List.foldl_append` and
their throughput a per-byte `ByteArray.push`. This `update` absorbs whole
blocks through `Fast.hashFrom`, so `update_append` is not a fold law. It is
reproved here from `hashFrom_add`, which splits a block run in two, and
`hashFrom_congr`, which says a block run depends only on the bytes it reads.

Every loop is `Nat.fold`, `List.ofFn`, or structural recursion; every index
carries a proof or goes through `Fast.byteAt`. No `Id.run do`, no `xs[i]!`
(`docs/SHA256-DAG.md` §3.3).
-/

namespace Sha256

/-! ## Block algebra of the byte-level reference

Two facts about `Impl.blocks` that only streaming needs. They are stated here,
in the module that needs them, rather than in `Sha256.Lengths`, which owns the
length and padding facts of the one-shot digest. -/

namespace Impl

/-- Cutting into blocks distributes over a concatenation whose left half is a
whole number of blocks. -/
theorem blocks_append (P Q : List UInt8) (h : P.length % 64 = 0) :
    blocks (P ++ Q) = blocks P ++ blocks Q := by
  by_cases hsmall : P.length < 64
  · have hnil : P = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil, List.nil_append, blocks_nil_of_lt [] (by simp), List.nil_append]
  · have hlen : ¬ ((P ++ Q).length < 64) := by rw [List.length_append]; omega
    have hdrop : (P.drop 64).length % 64 = 0 := by rw [List.length_drop]; omega
    rw [blocks_cons _ hlen, blocks_cons P hsmall,
      List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega), List.cons_append,
      blocks_append (P.drop 64) Q hdrop]
termination_by P.length
decreasing_by simp only [List.length_drop]; omega

/-- The buffered-update law at the level of the byte reference: hashing a
concatenation whose left half is a whole number of blocks is hashing the left
half and then continuing over the right half. -/
theorem hash'_append (P Q : List UInt8) (h : P.length % 64 = 0) :
    hash' (P ++ Q) = ((blocks Q).map wordsOfBlock).foldl compress (hash' P) := by
  rw [hash', hash', blocks_append P Q h, List.map_append, List.foldl_append]

end Impl

/-! ## Native-layer facts streaming needs

`Fast.hashFrom` runs a fixed number of blocks from an offset. Streaming needs
to split such a run in two, and to move a run onto another byte array that
holds the same bytes at a shifted offset. -/

namespace Fast

/-- A block run splits at any point. -/
theorem hashFrom_add (P : ByteArray) (m₁ : Nat) : ∀ (m₂ : Nat) (H : St) (off : Nat),
    hashFrom P H (m₁ + m₂) off = hashFrom P (hashFrom P H m₁ off) m₂ (off + 64 * m₁) := by
  induction m₁ with
  | zero => intro m₂ H off; rw [hashFrom, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  | succ m ih =>
      intro m₂ H off
      rw [show m + 1 + m₂ = (m + m₂) + 1 from by omega, hashFrom, hashFrom, ih,
        show off + 64 + 64 * m = off + 64 * (m + 1) from by omega]

/-- A block run reads exactly the `64 * m` bytes from its offset, so two byte
arrays that agree there give the same result. -/
theorem hashFrom_congr (P Q : ByteArray) (m : Nat) : ∀ (H : St) (offP offQ : Nat),
    (∀ i, i < 64 * m → byteAt P (offP + i) = byteAt Q (offQ + i)) →
    hashFrom P H m offP = hashFrom Q H m offQ := by
  induction m with
  | zero => intro H offP offQ _; rw [hashFrom, hashFrom]
  | succ m ih =>
      intro H offP offQ hb
      have hword : ∀ j : Nat, j < 64 → byteAt P (offP + j) = byteAt Q (offQ + j) :=
        fun j hj => hb j (by omega)
      have hw : wordsAt P offP = wordsAt Q offQ := by
        apply Vector.ext
        intro i hi
        rw [wordsAt, wordsAt, Vec.getElem_ofFn, Vec.getElem_ofFn, wordAt, wordAt,
          show offP + 4 * i + 1 = offP + (4 * i + 1) from by omega,
          show offP + 4 * i + 2 = offP + (4 * i + 2) from by omega,
          show offP + 4 * i + 3 = offP + (4 * i + 3) from by omega,
          show offQ + 4 * i + 1 = offQ + (4 * i + 1) from by omega,
          show offQ + 4 * i + 2 = offQ + (4 * i + 2) from by omega,
          show offQ + 4 * i + 3 = offQ + (4 * i + 3) from by omega,
          hword (4 * i) (by omega), hword (4 * i + 1) (by omega),
          hword (4 * i + 2) (by omega), hword (4 * i + 3) (by omega)]
      rw [hashFrom, hashFrom, hw]
      refine ih _ (offP + 64) (offQ + 64) fun i hi => ?_
      rw [show offP + 64 + i = offP + (64 + i) from by omega,
        show offQ + 64 + i = offQ + (64 + i) from by omega]
      exact hb (64 + i) (by omega)

/-- The bytes of `bs` from `off` onward. Built through `List.ofFn`, so it costs
the length of the tail and nothing more; streaming only ever calls it with a
tail shorter than one block. -/
def tailFrom (bs : ByteArray) (off : Nat) : ByteArray :=
  (List.ofFn (n := bs.size - off) fun i => byteAt bs (off + i.1)).toByteArray

theorem size_tailFrom (bs : ByteArray) (off : Nat) :
    (tailFrom bs off).size = bs.size - off := by
  rw [tailFrom, List.size_toByteArray, List.length_ofFn]

theorem toList_tailFrom (bs : ByteArray) (off : Nat) :
    (tailFrom bs off).data.toList = bs.data.toList.drop off := by
  rw [tailFrom, List.toList_data_toByteArray]
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, List.length_drop, Array.length_toList]
    rfl
  · intro i h1 h2
    rw [List.length_drop, Array.length_toList] at h2
    have hlt : off + i < bs.data.toList.length := by rw [Array.length_toList]; omega
    rw [List.getElem_ofFn, List.getElem_drop]
    show byteAt bs (off + i) = _
    rw [byteAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl

end Fast

/-! ## Byte-string plumbing local to streaming -/

private theorem toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

private theorem getD_drop (l : List UInt8) (m j : Nat) :
    (l.drop m).getD j 0 = l.getD (m + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_append_left (l r : List UInt8) (i : Nat) (h : i < l.length) :
    (l ++ r).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-! ## The context -/

/-- An incremental SHA-256 computation: the chaining state after every complete
64-byte block absorbed so far, the pending partial block, and the number of
complete blocks already folded into `state` (`docs/SHA256-DAG.md` §4 A1.S5). -/
structure Context where
  /-- The chaining state after `absorbedBlocks` complete blocks. -/
  state : Fast.St
  /-- The pending partial block. -/
  buffer : ByteArray
  /-- Number of complete blocks folded into `state`. -/
  absorbedBlocks : Nat
  /-- The pending block is never complete. -/
  buffer_lt : buffer.size < 64

namespace Context

/-- Two contexts agreeing on the three data fields are equal; the bound is a
proposition and carries no information. -/
theorem ext {a b : Context} (hs : a.state = b.state) (hb : a.buffer = b.buffer)
    (hn : a.absorbedBlocks = b.absorbedBlocks) : a = b := by
  cases a
  cases b
  subst hs
  subst hb
  subst hn
  rfl

/-- The empty computation: the FIPS 180-4 §5.3.3 initial hash value, no pending
bytes, no absorbed blocks. -/
def init : Context :=
  { state := Fast.H0, buffer := ByteArray.empty, absorbedBlocks := 0, buffer_lt := by decide }

/-- Absorb every whole block of `all` into `state`, keep the tail, and add the
absorbed blocks to `k`. Factored out of `update` so that the concatenation is
formed once and named. -/
def absorbInto (state : Fast.St) (k : Nat) (all : ByteArray) : Context :=
  { state := Fast.hashFrom all state (all.size / 64) 0
    buffer := Fast.tailFrom all (64 * (all.size / 64))
    absorbedBlocks := k + all.size / 64
    buffer_lt := by rw [Fast.size_tailFrom]; omega }

/-! The three projections, stated so that proofs never rewrite under the
structure literal, whose `buffer_lt` field depends on the block count. -/

theorem state_absorbInto (state : Fast.St) (k : Nat) (all : ByteArray) :
    (absorbInto state k all).state = Fast.hashFrom all state (all.size / 64) 0 := rfl

theorem buffer_absorbInto (state : Fast.St) (k : Nat) (all : ByteArray) :
    (absorbInto state k all).buffer = Fast.tailFrom all (64 * (all.size / 64)) := rfl

theorem absorbedBlocks_absorbInto (state : Fast.St) (k : Nat) (all : ByteArray) :
    (absorbInto state k all).absorbedBlocks = k + all.size / 64 := rfl

/-- Feed more bytes. -/
def update (c : Context) (chunk : ByteArray) : Context :=
  absorbInto c.state c.absorbedBlocks (c.buffer ++ chunk)

/-- Finish a computation whose already-padded pending bytes are `tail`. -/
def finalizeFrom (state : Fast.St) (tail : ByteArray) : Digest 32 :=
  ⟨Fast.squeeze (Fast.hashFrom tail state (tail.size / 64) 0), Fast.size_squeeze _⟩

/-- Pad the pending bytes with the total byte count and finish. -/
def finalize (c : Context) : Digest 32 :=
  finalizeFrom c.state (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size))

/-- `Absorbs c bs`: `c` is the context reached from `init` by feeding exactly
`bs`. A relation rather than a stored list, so a context carries no unbounded
data. -/
inductive Absorbs : Context → List UInt8 → Prop where
  /-- `init` has absorbed nothing. -/
  | empty : Absorbs init []
  /-- Feeding a chunk appends its bytes. -/
  | feed {c : Context} {bs : List UInt8} (h : Absorbs c bs) (chunk : ByteArray) :
      Absorbs (c.update chunk) (bs ++ chunk.data.toList)

theorem absorbs_init : Absorbs init [] := Absorbs.empty

theorem absorbs_update {c : Context} {bs : List UInt8} (h : Absorbs c bs) (chunk : ByteArray) :
    Absorbs (c.update chunk) (bs ++ chunk.data.toList) := Absorbs.feed h chunk

theorem size_buffer (c : Context) : c.buffer.size < 64 := c.buffer_lt

/-! ## The update laws -/

theorem update_empty (c : Context) : c.update ByteArray.empty = c := by
  have hempty : ByteArray.empty.data.toList = ([] : List UInt8) := rfl
  have hlist : (c.buffer ++ ByteArray.empty).data.toList = c.buffer.data.toList := by
    rw [toList_append, hempty, List.append_nil]
  have hsize : (c.buffer ++ ByteArray.empty).size = c.buffer.size := by
    rw [ByteArray.size_append]
    rfl
  have hn : (c.buffer ++ ByteArray.empty).size / 64 = 0 := by
    have := c.buffer_lt
    omega
  refine ext ?_ ?_ ?_
  · rw [update, state_absorbInto, hn, Fast.hashFrom]
  · refine Hex.byteArray_eq_of_data ?_
    rw [update, buffer_absorbInto, hn, Fast.toList_tailFrom, hlist, Nat.mul_zero, List.drop_zero]
  · rw [update, absorbedBlocks_absorbInto, hn, Nat.add_zero]

/-- Absorbing `A` and then `b` is absorbing `A ++ b`. This is the buffered
update law; `update_append` is its statement in terms of a context. -/
theorem absorbInto_append (state : Fast.St) (k : Nat) (A b : ByteArray) :
    (absorbInto state k A).update b = absorbInto state k (A ++ b) := by
  have hAlen : A.data.toList.length = A.size := Array.length_toList
  have hWlist : (A ++ b).data.toList = A.data.toList ++ b.data.toList := toList_append A b
  have hWsize : (A ++ b).size = A.size + b.size := ByteArray.size_append
  have hBlist : (Fast.tailFrom A (64 * (A.size / 64)) ++ b).data.toList
      = A.data.toList.drop (64 * (A.size / 64)) ++ b.data.toList := by
    rw [toList_append, Fast.toList_tailFrom]
  have hBsize : (Fast.tailFrom A (64 * (A.size / 64)) ++ b).size
      = A.size - 64 * (A.size / 64) + b.size := by
    rw [ByteArray.size_append, Fast.size_tailFrom]
  have hcount : (A ++ b).size / 64
      = A.size / 64 + (Fast.tailFrom A (64 * (A.size / 64)) ++ b).size / 64 := by
    rw [hWsize, hBsize]
    omega
  have hprefix : 64 * (A.size / 64) ≤ A.data.toList.length := by omega
  have hfirst : Fast.hashFrom (A ++ b) state (A.size / 64) 0
      = Fast.hashFrom A state (A.size / 64) 0 := by
    refine Fast.hashFrom_congr (A ++ b) A (A.size / 64) state 0 0 fun i hi => ?_
    rw [Fast.byteAt_eq, Fast.byteAt_eq, hWlist, Nat.zero_add,
      getD_append_left _ _ _ (by omega)]
  have hsecond : ∀ H : Fast.St,
      Fast.hashFrom (A ++ b) H ((Fast.tailFrom A (64 * (A.size / 64)) ++ b).size / 64)
          (0 + 64 * (A.size / 64))
        = Fast.hashFrom (Fast.tailFrom A (64 * (A.size / 64)) ++ b) H
            ((Fast.tailFrom A (64 * (A.size / 64)) ++ b).size / 64) 0 := by
    intro H
    refine Fast.hashFrom_congr _ _ _ H _ 0 fun i _ => ?_
    rw [Fast.byteAt_eq, Fast.byteAt_eq, hWlist, hBlist, Nat.zero_add, Nat.zero_add,
      ← List.drop_append_of_le_length (l₂ := b.data.toList) hprefix, ← getD_drop]
  show absorbInto (Fast.hashFrom A state (A.size / 64) 0) (k + A.size / 64)
      (Fast.tailFrom A (64 * (A.size / 64)) ++ b) = absorbInto state k (A ++ b)
  refine ext ?_ ?_ ?_
  · rw [state_absorbInto, state_absorbInto, hcount, Fast.hashFrom_add, hfirst, hsecond]
  · refine Hex.byteArray_eq_of_data ?_
    rw [buffer_absorbInto, buffer_absorbInto, Fast.toList_tailFrom, Fast.toList_tailFrom,
      hBlist, hWlist, ← List.drop_append_of_le_length (l₂ := b.data.toList) hprefix,
      List.drop_drop, hcount]
    congr 1
    omega
  · rw [absorbedBlocks_absorbInto, absorbedBlocks_absorbInto, hcount, Nat.add_assoc]

/-- The buffered-update law: feeding two chunks in turn is feeding their
concatenation. -/
theorem update_append (c : Context) (a b : ByteArray) :
    (c.update a).update b = c.update (a ++ b) := by
  have hassoc : c.buffer ++ (a ++ b) = (c.buffer ++ a) ++ b :=
    Hex.byteArray_eq_of_data (by
      rw [toList_append, toList_append, toList_append, toList_append, List.append_assoc])
  show (absorbInto c.state c.absorbedBlocks (c.buffer ++ a)).update b
      = absorbInto c.state c.absorbedBlocks (c.buffer ++ (a ++ b))
  rw [absorbInto_append, hassoc]

/-! ## The state invariant

`Absorbs` says which bytes a context came from; `Sound` says what that forces
its three fields to be. `sound_of_absorbs` is the induction, and everything the
digest theorems need comes out of `Sound`. -/

/-- The invariant every reachable context satisfies against its input. -/
structure Sound (c : Context) (bs : List UInt8) : Prop where
  /-- `64 * absorbedBlocks` bytes really are there. -/
  length_prefix : (bs.take (64 * c.absorbedBlocks)).length = 64 * c.absorbedBlocks
  /-- The pending buffer is exactly the rest of the input. -/
  split : bs.take (64 * c.absorbedBlocks) ++ c.buffer.data.toList = bs
  /-- The state is the byte reference's hash of the absorbed prefix. -/
  state_eq : Fast.abs c.state = Impl.hash' (bs.take (64 * c.absorbedBlocks))

theorem sound_of_absorbs {c : Context} {bs : List UInt8} (h : Absorbs c bs) : Sound c bs := by
  induction h with
  | empty =>
      refine ⟨rfl, rfl, ?_⟩
      show Fast.abs Fast.H0 = Impl.hash' []
      rw [Fast.H0_eq, Impl.hash', Impl.blocks_nil_of_lt [] (by simp)]
      rfl
  | @feed c bs _ chunk ih =>
      have hk := ih.length_prefix
      have hsplit := ih.split
      have hstate := ih.state_eq
      have hAlen : (c.buffer ++ chunk).data.toList.length = (c.buffer ++ chunk).size :=
        Array.length_toList
      have hbs' : bs ++ chunk.data.toList
          = bs.take (64 * c.absorbedBlocks) ++ (c.buffer ++ chunk).data.toList := by
        rw [toList_append, ← List.append_assoc, hsplit]
      have hnewk : (c.update chunk).absorbedBlocks
          = c.absorbedBlocks + (c.buffer ++ chunk).size / 64 :=
        absorbedBlocks_absorbInto _ _ _
      have htake : (bs ++ chunk.data.toList).take
            (64 * (c.absorbedBlocks + (c.buffer ++ chunk).size / 64))
          = bs.take (64 * c.absorbedBlocks)
            ++ (c.buffer ++ chunk).data.toList.take (64 * ((c.buffer ++ chunk).size / 64)) := by
        rw [hbs',
          show 64 * (c.absorbedBlocks + (c.buffer ++ chunk).size / 64)
            = (bs.take (64 * c.absorbedBlocks)).length
              + 64 * ((c.buffer ++ chunk).size / 64) from by omega,
          List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          show (bs.take (64 * c.absorbedBlocks)).length
              + 64 * ((c.buffer ++ chunk).size / 64)
              - (bs.take (64 * c.absorbedBlocks)).length
            = 64 * ((c.buffer ++ chunk).size / 64) from by omega]
      have hlenA : ((c.buffer ++ chunk).data.toList.take
            (64 * ((c.buffer ++ chunk).size / 64))).length
          = 64 * ((c.buffer ++ chunk).size / 64) := by
        rw [List.length_take]
        omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hnewk, htake, List.length_append, hlenA, hk]
        omega
      · rw [hnewk, htake, update, buffer_absorbInto, Fast.toList_tailFrom, List.append_assoc,
          List.take_append_drop, hbs']
      · rw [hnewk, htake, Impl.hash'_append _ _ (by omega), update, state_absorbInto,
          Fast.hashFrom_abs (c.buffer ++ chunk) ((c.buffer ++ chunk).size / 64) c.state 0
            (by omega),
          List.drop_zero, hstate]

/-! ## The digest theorems -/

/-- The incremental digest of exactly the bytes fed is the one-shot digest of
those bytes. `Sha256.Bridge.sha256_bridge` then makes it the FIPS 180-4
function. -/
theorem finalize_absorbs {c : Context} {bs : List UInt8} (h : Absorbs c bs) :
    c.finalize.toList = Impl.sha256 bs := by
  have hs := sound_of_absorbs h
  have hbuflen : c.buffer.data.toList.length = c.buffer.size := Array.length_toList
  have hrlt : c.buffer.size < 64 := c.buffer_lt
  have hbslen : bs.length = 64 * c.absorbedBlocks + c.buffer.size := by
    rw [← hs.split, List.length_append, hs.length_prefix, hbuflen]
  have hsuffix : (Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).data.toList
      = (0x80 :: List.replicate
            ((119 - (64 * c.absorbedBlocks + c.buffer.size) % 64) % 64) 0)
        ++ Impl.lengthBytes (8 * (64 * c.absorbedBlocks + c.buffer.size)) := by
    rw [Fast.padSuffix, List.toList_data_toByteArray]
  have hTlist : (c.buffer
        ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).data.toList
      = c.buffer.data.toList
        ++ ((0x80 :: List.replicate
              ((119 - (64 * c.absorbedBlocks + c.buffer.size) % 64) % 64) 0)
          ++ Impl.lengthBytes (8 * (64 * c.absorbedBlocks + c.buffer.size))) := by
    rw [toList_append, hsuffix]
  have hTlen : (c.buffer
        ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).data.toList.length
      = c.buffer.size + 1
        + (119 - (64 * c.absorbedBlocks + c.buffer.size) % 64) % 64 + 8 := by
    rw [hTlist, List.length_append, List.length_append, List.length_cons,
      List.length_replicate, Impl.length_lengthBytes, hbuflen]
    omega
  have hTsize : (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).size
      = c.buffer.size + 1
        + (119 - (64 * c.absorbedBlocks + c.buffer.size) % 64) % 64 + 8 := by
    rw [← hTlen]
    exact (Array.length_toList).symm
  have hTblocks : 64 * ((c.buffer
        ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).size / 64)
      = (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).size := by
    rw [hTsize]
    omega
  have hpad : Impl.padBytes bs = bs.take (64 * c.absorbedBlocks)
      ++ (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).data.toList := by
    rw [hTlist, ← List.append_assoc, hs.split, Impl.padBytes, hbslen]
  have hTle : (c.buffer
        ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).data.toList.length
      ≤ (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).size := by
    omega
  rw [Impl.sha256, finalize, finalizeFrom]
  show (Fast.squeeze _).data.toList = _
  rw [Fast.squeeze_eq,
    Fast.hashFrom_abs (c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size))
      ((c.buffer ++ Fast.padSuffix (64 * c.absorbedBlocks + c.buffer.size)).size / 64)
      c.state 0 (by omega),
    List.drop_zero, hTblocks, List.take_of_length_le hTle, hs.state_eq,
    ← Impl.hash'_append _ _ (by rw [hs.length_prefix]; omega), ← hpad, Impl.hash]

/-- Feeding a whole message to a fresh context is the public `Sha256.sha256`. -/
theorem finalize_init_update (m : ByteArray) : (init.update m).finalize = sha256 m := by
  refine Digest.ext (Hex.byteArray_eq_of_data ?_)
  show (init.update m).finalize.toList = (sha256 m).toList
  rw [finalize_absorbs (absorbs_update absorbs_init m), List.nil_append, sha256_impl]

end Context

end Sha256
