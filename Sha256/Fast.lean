import Sha256.Lengths

/-!
# `Sha256.Fast` — the native layer

`Sha256.Impl` mirrored line for line with `UInt32` for `BitVec 32`, `rotr` for
`BitVec.rotateRight`, `byteAt` for `List.getD`, and `ByteArray` for
`List UInt8`. `sha256_eq_impl` proves the two agree on every input, so nothing
new is claimed here: the meaning still comes from `Sha256.Bridge.sha256_bridge`.

The split exists for one measured reason (`docs/SHA256-DAG.md` §2, refuting the
coordinator's P0 prediction): identical rotate/xor/shift/add work over `10⁷`
iterations costs 6572.78 ms on `BitVec 32` against 8.90 ms on `UInt32`, a factor
of 738, because `BitVec` arithmetic allocates and wraps through `Fin`. In the
kernel the picture inverts, which is why the known-answer tests stay on `Impl`.

Every loop is `Nat.fold`, `Sha256.Vec.ofFn`, or structural recursion; every
index carries a proof or goes through `byteAt`. No `Id.run do`, no `xs[i]!`.
-/

namespace Sha256.Fast

open Sha256

/-- FIPS 180-4 §3.1 at native width. -/
abbrev Word := UInt32

/-- The eight-word hash state of FIPS 180-4 §6.2.2, at native width. -/
abbrev St := Vector Word 8

/-- Abstraction to the proved layer. -/
def abs (s : St) : Impl.St := s.map UInt32.toBitVec

/-! ## §4.1.2 — the logical functions, at native width -/

/-- Rotate right. Core has no `UInt32.rotateRight`; `toBitVec_rotr` proves this
is `BitVec.rotateRight`. -/
def rotr (x : Word) (n : Nat) : Word := (x >>> n.toUInt32) ||| (x <<< (32 - n).toUInt32)

/-- FIPS 180-4 §4.1.2 (4.2). -/
def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 §4.1.2 (4.3). -/
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2 (4.4). -/
def «Σ0» (x : Word) : Word := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- FIPS 180-4 §4.1.2 (4.5). -/
def «Σ1» (x : Word) : Word := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- FIPS 180-4 §4.1.2 (4.6). -/
def σ0 (x : Word) : Word := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- FIPS 180-4 §4.1.2 (4.7). -/
def σ1 (x : Word) : Word := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- FIPS 180-4 §4.2.2, the same sixty-four literals as `Spec.K`; `K_eq` pins
that they are the same. -/
def K : Vector Word 64 :=
  #v[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- FIPS 180-4 §5.3.3, the same eight literals as `Spec.H0`; `H0_eq` pins it. -/
def H0 : St :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## Word-level abstraction lemmas

Each is `toBitVec` commuting with one operator. The `UInt32.toBitVec_*` lemmas
of `Init/Data/UInt/Bitwise.lean` are all `rfl`, so at a literal rotation amount
the rotate lemma is `rfl` too. -/

private theorem shiftAmount (m : Nat) (h : m < 32) :
    ((m.toUInt32).toBitVec % 32).toNat = m := by
  have hm : ((m.toUInt32).toBitVec).toNat = m % 2 ^ 32 := UInt32.toNat_ofNat'
  have h32 : m < 2 ^ 32 := Nat.lt_of_lt_of_le h (by decide)
  rw [BitVec.toNat_umod, hm, Nat.mod_eq_of_lt h32,
    show ((32 : BitVec 32)).toNat = 32 from rfl, Nat.mod_eq_of_lt h]

theorem toBitVec_rotr (x : Word) (n : Nat) (h : n < 32) :
    (rotr x n).toBitVec = x.toBitVec.rotateRight n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [rotr, BitVec.rotateRight_def]
  · rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h]
    simp only [rotr, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
      BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', shiftAmount n h,
      shiftAmount (32 - n) (by omega)]

theorem Ch_abs (x y z : Word) :
    (Ch x y z).toBitVec = Spec.Ch x.toBitVec y.toBitVec z.toBitVec := rfl

theorem Maj_abs (x y z : Word) :
    (Maj x y z).toBitVec = Spec.Maj x.toBitVec y.toBitVec z.toBitVec := rfl

theorem Sigma0_abs (x : Word) : («Σ0» x).toBitVec = Spec.«Σ0» x.toBitVec := rfl

theorem Sigma1_abs (x : Word) : («Σ1» x).toBitVec = Spec.«Σ1» x.toBitVec := rfl

theorem sigma0_abs (x : Word) : (σ0 x).toBitVec = Spec.σ0 x.toBitVec := rfl

theorem sigma1_abs (x : Word) : (σ1 x).toBitVec = Spec.σ1 x.toBitVec := rfl

private theorem K_eq_all : ∀ j : Fin 64, (K[j.1]).toBitVec = Spec.K[j.1] := by decide

theorem K_eq (i : Nat) (h : i < 64) : (K[i]).toBitVec = Spec.K[i] := K_eq_all ⟨i, h⟩

theorem H0_eq : abs H0 = Spec.H0 := by
  apply Vector.ext
  intro i hi
  rw [abs, Vector.getElem_map]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

/-! ## The `Nat.fold` transport lemma

Every bounded loop in `Spec` and `Fast` is a `Nat.fold` over the same bound with
the same step shape. This is the one induction that carries all of them. -/

theorem fold_abs {α β : Type} (φ : α → β) :
    ∀ (n : Nat) (f : (i : Nat) → i < n → α → α) (g : (i : Nat) → i < n → β → β),
      (∀ i hi a, φ (f i hi a) = g i hi (φ a)) → ∀ a, φ (Nat.fold n f a) = Nat.fold n g (φ a) := by
  intro n
  induction n with
  | zero => intro f g _ a; simp
  | succ n ih =>
      intro f g hstep a
      rw [Nat.fold_succ, Nat.fold_succ, hstep,
        ih (fun i _ => f i (by omega)) (fun i _ => g i (by omega))
          (fun i hi b => hstep i (by omega) b) a]

/-! ## §6.2.2 step 1 — the message schedule -/

def scheduleInit (w : Vector Word 16) : Vector Word 64 :=
  Vec.ofFn fun i : Fin 64 => if h : i.val < 16 then w[i.val] else 0

def scheduleStep (i : Nat) (hi : i < 48) (acc : Vector Word 64) : Vector Word 64 :=
  have h2 : i + 16 - 2 < 64 := by omega
  have h7 : i + 16 - 7 < 64 := by omega
  have h15 : i + 16 - 15 < 64 := by omega
  have h16 : i + 16 - 16 < 64 := by omega
  acc.set (i + 16)
    (σ1 acc[i + 16 - 2] + acc[i + 16 - 7] + σ0 acc[i + 16 - 15] + acc[i + 16 - 16])
    (by omega)

def schedule (w : Vector Word 16) : Vector Word 64 :=
  Nat.fold 48 scheduleStep (scheduleInit w)

theorem scheduleInit_abs (w : Vector Word 16) :
    (scheduleInit w).map UInt32.toBitVec = Spec.scheduleInit (w.map UInt32.toBitVec) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, scheduleInit, Spec.scheduleInit, Vec.getElem_ofFn, Vec.getElem_ofFn]
  by_cases h16 : i < 16
  · rw [dif_pos h16, dif_pos h16, Vector.getElem_map]
  · rw [dif_neg h16, dif_neg h16]
    rfl

theorem scheduleStep_abs (i : Nat) (hi : i < 48) (acc : Vector Word 64) :
    (scheduleStep i hi acc).map UInt32.toBitVec
      = Spec.scheduleStep i hi (acc.map UInt32.toBitVec) := by
  rw [scheduleStep, Spec.scheduleStep, Vector.map_set]
  congr 1
  simp only [UInt32.toBitVec_add, sigma0_abs, sigma1_abs,
    Vector.getElem_map (f := UInt32.toBitVec)]

theorem schedule_abs (w : Vector Word 16) :
    (schedule w).map UInt32.toBitVec = Impl.schedule (w.map UInt32.toBitVec) := by
  rw [schedule, Impl.schedule, Spec.schedule, ← scheduleInit_abs]
  exact fold_abs (Vector.map UInt32.toBitVec) 48 _ _ scheduleStep_abs _

/-! ## §6.2.2 steps 2–4 — compression -/

def round (sched : Vector Word 64) (t : Nat) (ht : t < 64) (st : St) : St :=
  let a := st[0]
  let b := st[1]
  let c := st[2]
  let d := st[3]
  let e := st[4]
  let f := st[5]
  let g := st[6]
  let h := st[7]
  let T1 := h + «Σ1» e + Ch e f g + K[t] + sched[t]
  let T2 := «Σ0» a + Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

def compress (H : St) (w : Vector Word 16) : St :=
  let final := Nat.fold 64 (round (schedule w)) H
  Vec.ofFn fun i : Fin 8 =>
    have hi : i.1 < 8 := i.2
    H[i.1] + final[i.1]

private theorem map_v8 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector Word 8).map UInt32.toBitVec
      = #v[x0.toBitVec, x1.toBitVec, x2.toBitVec, x3.toBitVec,
           x4.toBitVec, x5.toBitVec, x6.toBitVec, x7.toBitVec] := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

theorem round_abs (sched : Vector Word 64) (t : Nat) (ht : t < 64) (st : St) :
    (round sched t ht st).map UInt32.toBitVec
      = Spec.round (sched.map UInt32.toBitVec) t ht (st.map UInt32.toBitVec) := by
  rw [round, Spec.round, map_v8]
  simp only [UInt32.toBitVec_add, Ch_abs, Maj_abs, Sigma0_abs, Sigma1_abs,
    Vector.getElem_map (f := UInt32.toBitVec), K_eq t ht]

theorem compress_abs (H : St) (w : Vector Word 16) :
    abs (compress H w) = Impl.compress (abs H) (w.map UInt32.toBitVec) := by
  have hfinal : (Nat.fold 64 (round (schedule w)) H).map UInt32.toBitVec
      = Nat.fold 64 (Spec.round (Spec.schedule (w.map UInt32.toBitVec)))
          (H.map UInt32.toBitVec) := by
    have h1 : (schedule w).map UInt32.toBitVec = Spec.schedule (w.map UInt32.toBitVec) :=
      schedule_abs w
    rw [← h1]
    exact fold_abs (Vector.map UInt32.toBitVec) 64 _ _
      (fun t ht st => round_abs (schedule w) t ht st) H
  simp only [abs, compress, Impl.compress, Spec.compress]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, Vec.getElem_ofFn, Vec.getElem_ofFn, UInt32.toBitVec_add,
    ← Vector.getElem_map (f := UInt32.toBitVec) (xs := H) hi,
    ← Vector.getElem_map (f := UInt32.toBitVec)
      (xs := Nat.fold 64 (round (schedule w)) H) hi,
    hfinal]

/-! ## Bytes -/

/-- Total byte read: no panic path. `byteAt_eq` proves it is `List.getD _ 0`. -/
def byteAt (bs : ByteArray) (i : Nat) : UInt8 := if h : i < bs.size then bs[i] else 0

theorem byteAt_eq (bs : ByteArray) (i : Nat) : byteAt bs i = bs.data.toList.getD i 0 := by
  have hsz : bs.size = bs.data.toList.length := (Array.length_toList).symm
  rw [byteAt]
  by_cases h : i < bs.size
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- Big-endian word `i` of the 64-byte block at `off`; absent bytes read `0`. -/
def wordAt (bs : ByteArray) (off i : Nat) : Word :=
  ((byteAt bs (off + 4 * i)).toUInt32 <<< 24) |||
    (((byteAt bs (off + 4 * i + 1)).toUInt32 <<< 16) |||
      (((byteAt bs (off + 4 * i + 2)).toUInt32 <<< 8) |||
        (byteAt bs (off + 4 * i + 3)).toUInt32))

def wordsAt (bs : ByteArray) (off : Nat) : Vector Word 16 :=
  Vec.ofFn fun i : Fin 16 => wordAt bs off i.1

private theorem toUInt32_toBitVec (b : UInt8) :
    b.toUInt32.toBitVec = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (b.toUInt32.toBitVec).toNat = b.toNat := UInt8.toNat_toUInt32 b
  rw [h1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.toNat_lt (by decide))]

private theorem toBitVec_wordAt (bs : ByteArray) (off i : Nat) :
    (wordAt bs off i).toBitVec =
      Impl.wordOfBytes (byteAt bs (off + 4 * i)) (byteAt bs (off + 4 * i + 1))
        (byteAt bs (off + 4 * i + 2)) (byteAt bs (off + 4 * i + 3)) := by
  rw [wordAt, Impl.wordOfBytes]
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, toUInt32_toBitVec]
  rfl

private theorem getD_take_drop (l : List UInt8) (off k : Nat) (h : k < 64) :
    ((l.drop off).take 64).getD k 0 = l.getD (off + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, h]

theorem wordsAt_eq (bs : ByteArray) (off : Nat) :
    (wordsAt bs off).map UInt32.toBitVec
      = Impl.wordsOfBlock ((bs.data.toList.drop off).take 64) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_map, wordsAt, Vec.getElem_ofFn, Impl.wordsOfBlock, Vec.getElem_ofFn,
    toBitVec_wordAt, byteAt_eq, byteAt_eq, byteAt_eq, byteAt_eq,
    getD_take_drop _ _ _ (by omega), getD_take_drop _ _ _ (by omega),
    getD_take_drop _ _ _ (by omega), getD_take_drop _ _ _ (by omega)]
  simp only [Nat.add_assoc]

/-! ## §5.1.1 — padding -/

/-- The padding bytes for a message of `n` bytes: at most 72 of them, so
building them through a list costs nothing measurable. -/
def padSuffix (n : Nat) : ByteArray :=
  ((0x80 :: List.replicate ((119 - n % 64) % 64) (0 : UInt8)) ++
    Impl.lengthBytes (8 * n)).toByteArray

def padBytes (msg : ByteArray) : ByteArray := msg ++ padSuffix msg.size

theorem padBytes_eq (msg : ByteArray) :
    (padBytes msg).data.toList = Impl.padBytes msg.data.toList := by
  have hsize : msg.size = msg.data.toList.length := (Array.length_toList).symm
  rw [padBytes, padSuffix, Impl.padBytes, ByteArray.data_append, Array.toList_append,
    List.toList_data_toByteArray, hsize]

/-! ## §6.2 — the hash computation -/

/-- `List.drop_take` reaches `Classical.choice` in v4.33.1 core (measured with
`#print axioms`), which the ceiling of `docs/SHA256-DAG.md` §3.1 forbids for
this tree. The same statement by structural induction is `[propext]`. -/
private theorem drop_take {α : Type} (i j : Nat) (l : List α) :
    (l.take j).drop i = (l.drop i).take (j - i) := by
  induction i generalizing j l with
  | zero => simp
  | succ i ih =>
      cases l with
      | nil => simp
      | cons a t =>
          cases j with
          | zero => simp
          | succ j =>
              rw [List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons, ih,
                show j + 1 - (i + 1) = j - i from by omega]

/-- `m` blocks of 64 bytes starting at `off`, folded from the front. Structural
recursion on the block count, and tail recursive. -/
def hashFrom (P : ByteArray) : St → Nat → Nat → St
  | H, 0, _ => H
  | H, m + 1, off => hashFrom P (compress H (wordsAt P off)) m (off + 64)

def hashAll (P : ByteArray) : St := hashFrom P H0 (P.size / 64) 0

theorem hashFrom_abs (P : ByteArray) (m : Nat) : ∀ (H : St) (off : Nat),
    off + 64 * m ≤ P.size →
    abs (hashFrom P H m off) =
      ((Impl.blocks ((P.data.toList.drop off).take (64 * m))).map Impl.wordsOfBlock).foldl
        Impl.compress (abs H) := by
  induction m with
  | zero =>
      intro H off _
      rw [hashFrom, Nat.mul_zero, List.take_zero,
        Impl.blocks_nil_of_lt _ (by simp), List.map_nil, List.foldl_nil]
  | succ m ih =>
      intro H off hb
      have hlen : (P.data.toList.drop off).length = P.size - off := by
        rw [List.length_drop, Array.length_toList]
        rfl
      have hblock : ((P.data.toList.drop off).take (64 * (m + 1))).length = 64 * (m + 1) := by
        rw [List.length_take, hlen]
        omega
      have hbig : ¬ (((P.data.toList.drop off).take (64 * (m + 1))).length < 64) := by
        rw [hblock]; omega
      have htake : ((P.data.toList.drop off).take (64 * (m + 1))).take 64
          = (P.data.toList.drop off).take 64 := by
        rw [List.take_take, show min 64 (64 * (m + 1)) = 64 from by omega]
      have hdrop : ((P.data.toList.drop off).take (64 * (m + 1))).drop 64
          = (P.data.toList.drop (off + 64)).take (64 * m) := by
        rw [drop_take, List.drop_drop, show 64 * (m + 1) - 64 = 64 * m from by omega]
      rw [hashFrom, ih _ _ (by omega), compress_abs, wordsAt_eq,
        Impl.blocks_cons _ hbig, List.map_cons, List.foldl_cons, htake, hdrop]

/-- `Impl.blocks` ignores a trailing run shorter than a block, so truncating to
a whole number of blocks first changes nothing. -/
theorem blocks_take_multiple (L : List UInt8) :
    Impl.blocks (L.take (64 * (L.length / 64))) = Impl.blocks L := by
  by_cases hsmall : L.length < 64
  · have h0 : 64 * (L.length / 64) = 0 := by omega
    rw [h0, List.take_zero, Impl.blocks_nil_of_lt _ (by simp),
      Impl.blocks_nil_of_lt _ hsmall]
  · have hlen : (L.take (64 * (L.length / 64))).length = 64 * (L.length / 64) := by
      rw [List.length_take]; omega
    have hbig : ¬ ((L.take (64 * (L.length / 64))).length < 64) := by rw [hlen]; omega
    have htake : (L.take (64 * (L.length / 64))).take 64 = L.take 64 := by
      rw [List.take_take, show min 64 (64 * (L.length / 64)) = 64 from by omega]
    have hdrop : (L.take (64 * (L.length / 64))).drop 64
        = (L.drop 64).take (64 * ((L.drop 64).length / 64)) := by
      rw [drop_take, List.length_drop]
      congr 1
      omega
    rw [Impl.blocks_cons _ hbig, Impl.blocks_cons _ hsmall, htake, hdrop,
      blocks_take_multiple (L.drop 64)]
termination_by L.length
decreasing_by simp only [List.length_drop]; omega

theorem hashAll_abs (P : ByteArray) : abs (hashAll P) = Impl.hash' P.data.toList := by
  have hsize : P.data.toList.length = P.size := Array.length_toList
  rw [hashAll, hashFrom_abs P (P.size / 64) H0 0 (by omega), List.drop_zero, H0_eq,
    show 64 * (P.size / 64) = 64 * (P.data.toList.length / 64) by rw [hsize],
    blocks_take_multiple, Impl.hash']

/-! ## §3.1 — the output -/

def bytesOfWord (w : Word) : List UInt8 :=
  [UInt8.ofNat (w >>> 24).toNat, UInt8.ofNat (w >>> 16).toNat,
   UInt8.ofNat (w >>> 8).toNat, UInt8.ofNat w.toNat]

private theorem bytesOfWord_eq (w : Word) : bytesOfWord w = Impl.bytesOfWord w.toBitVec := rfl

private theorem getElem_abs (H : St) (i : Fin 8) : (abs H)[i] = (H[i]).toBitVec :=
  Vector.getElem_map _ i.2

def squeeze (H : St) : ByteArray :=
  ((List.finRange 8).flatMap fun i => bytesOfWord H[i]).toByteArray

theorem squeeze_eq (H : St) :
    (squeeze H).data.toList
      = (List.finRange 8).flatMap fun i => Impl.bytesOfWord (abs H)[i] := by
  rw [squeeze, List.toList_data_toByteArray]
  simp only [bytesOfWord_eq, getElem_abs]

theorem size_squeeze (H : St) : (squeeze H).size = 32 := by
  rw [squeeze, List.size_toByteArray, Spec.length_flatMap_const _ _ 4 fun _ => rfl]
  simp

/-! ## The apex of the native layer -/

def sha256 (msg : ByteArray) : ByteArray := squeeze (hashAll (padBytes msg))

theorem sha256_eq_impl (msg : ByteArray) :
    (sha256 msg).data.toList = Impl.sha256 msg.data.toList := by
  rw [sha256, squeeze_eq, hashAll_abs, padBytes_eq, Impl.sha256, Impl.hash]

theorem size_sha256 (msg : ByteArray) : (sha256 msg).size = 32 := size_squeeze _

end Sha256.Fast
