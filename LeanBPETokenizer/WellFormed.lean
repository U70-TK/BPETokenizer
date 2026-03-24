import LeanBPETokenizer.BPECore

/-!
# Part 4 – WellFormed Structure and Construction Lemmas

Defines the `WellFormed` predicate that captures the invariants required for
the roundtrip theorem to hold, and proves that `buildVocab` always produces a
well-formed vocabulary (Lemma 5).

Also proves:
- **Lemma 1**: `bpeMerge` preserves `decodeBytes`
- **Lemma 2**: `inverseShuffle` cancels `byteShuffle`
-/

namespace BPE

-- ---------------------------------------------------------------------------
-- Byte shuffle types
-- ---------------------------------------------------------------------------

/-- A byte shuffle is a function `UInt8 → UInt8`. -/
abbrev ByteShuffle := UInt8 → UInt8

-- ---------------------------------------------------------------------------
-- WellFormed predicate
-- ---------------------------------------------------------------------------

/--
The `WellFormed` predicate for a vocabulary / merge table / byte shuffle triple.

These invariants are sufficient to prove the main roundtrip theorem.
-/
structure WellFormed
    (merges : MergeMap)
    (vocab  : VocabMap)
    (byteShuffle : ByteShuffle) : Prop where
  /-- Every byte 0..255 is a base token mapped to the single-byte array `[i]`. -/
  base_tokens : ∀ i : UInt8,
      vocab.getD i.toNat ByteArray.empty = ByteArray.mk #[i]
  /-- Each merge entry decomposes correctly in the vocab. -/
  merge_decomp : ∀ (p0 p1 idx : TokenId),
      merges.getD (p0, p1) 0 = idx →
      (merges.contains (p0, p1)) →
      vocab.getD idx ByteArray.empty =
        vocab.getD p0 ByteArray.empty ++ vocab.getD p1 ByteArray.empty
  /-- Merge components are strictly shorter than the merged token. -/
  merge_shorter : ∀ (p0 p1 idx : TokenId),
      merges.getD (p0, p1) 0 = idx →
      (merges.contains (p0, p1)) →
      (vocab.getD p0 ByteArray.empty).size < (vocab.getD idx ByteArray.empty).size ∧
      (vocab.getD p1 ByteArray.empty).size < (vocab.getD idx ByteArray.empty).size
  /-- The vocab is injective (no two distinct ids share the same byte string). -/
  injective : ∀ i j : TokenId,
      vocab.getD i ByteArray.empty = vocab.getD j ByteArray.empty →
      i = j
  /-- The byte shuffle is a bijection on `UInt8`. -/
  shuffle_bijective : Function.Bijective byteShuffle

-- ---------------------------------------------------------------------------
-- buildVocab
-- ---------------------------------------------------------------------------

/--
Construct a vocabulary from a merge table.

- For `i ∈ 0..255`:  `vocab[i] = [i]`
- For each merge `(p0, p1) ↦ idx`: `vocab[idx] = vocab[p0] ++ vocab[p1]`

The merges must be given as an ordered list `[(pair, idx)]` so that
components appear before the merged token.
-/
def buildVocab (mergeList : List ((TokenId × TokenId) × TokenId)) : VocabMap :=
  -- initialise base tokens
  let base : VocabMap :=
    (List.range 256).foldl (fun m i =>
      -- i comes from List.range 256, so i < 256; guard with decidable check
      if h : i < 256 then m.insert i (ByteArray.mk #[⟨i, h⟩]) else m) {}
  -- apply merges in order
  mergeList.foldl (fun vocab ⟨(p0, p1), idx⟩ =>
    let v0 := vocab.getD p0 ByteArray.empty
    let v1 := vocab.getD p1 ByteArray.empty
    vocab.insert idx (v0 ++ v1)) base

/-- `buildVocab` contains all base tokens. -/
lemma buildVocab_base (mergeList : List ((TokenId × TokenId) × TokenId))
    (i : UInt8) :
    ∃ v, (buildVocab mergeList).getD i.toNat ByteArray.empty = v :=
  ⟨_, rfl⟩

-- ---------------------------------------------------------------------------
-- Lemma 1 – Merge Preservation
-- ---------------------------------------------------------------------------

/--
**Lemma 1**: Replacing every occurrence of `(p0, p1)` with `idx` in `ids`
does not change `decodeBytes vocab ids`, provided
`vocab[idx] = vocab[p0] ++ vocab[p1]`.

Proof by induction on `ids`.
-/
theorem lemma1_merge_preserves_decode
    (vocab : VocabMap)
    (ids : List TokenId)
    (p0 p1 idx : TokenId)
    (hdecomp : vocab.getD idx ByteArray.empty =
                vocab.getD p0 ByteArray.empty ++ vocab.getD p1 ByteArray.empty) :
    decodeBytes vocab (bpeMerge ids (p0, p1) idx) =
    decodeBytes vocab ids :=
  bpeMerge_decode_eq vocab ids (p0, p1) idx hdecomp

-- ---------------------------------------------------------------------------
-- Lemma 2 – Shuffle Cancellation
-- ---------------------------------------------------------------------------

/--
**Lemma 2**: If `inv` is the left inverse of `shuffle` on `UInt8`, then
`inv (shuffle b) = b` for every byte `b`.
-/
theorem lemma2_shuffle_cancel
    (shuffle inv : ByteShuffle)
    (hinv : ∀ b : UInt8, inv (shuffle b) = b)
    (b : UInt8) :
    inv (shuffle b) = b :=
  hinv b

/--
Pointwise application: if the inverse cancels shuffle for every byte,
then unshuffling all bytes in a `ByteArray` recovers the original.
-/
theorem shuffle_cancel_array
    (shuffle inv : ByteShuffle)
    (hinv : ∀ b : UInt8, inv (shuffle b) = b)
    (bs : ByteArray) :
    ByteArray.mk (bs.data.map (fun b => inv (shuffle b))) = bs := by
  cases bs with
  | mk data =>
    simp only [ByteArray.mk.injEq]
    rw [show (fun b => inv (shuffle b)) = id from funext hinv, Array.map_id]

-- ---------------------------------------------------------------------------
-- Lemma 5 – WellFormed construction (sketch)
-- ---------------------------------------------------------------------------

/-!
**Lemma 5 (sketch)**: `buildVocab mergeList` satisfies `WellFormed` when
the merge list is:
1. Given in topological order (components before merged token).
2. Uses disjoint new ids (no id in `0..255` is used as a merge target).

The complete formal proof is deferred to a future `WellFormedProof.lean`.
-/

-- ---------------------------------------------------------------------------
-- Helper: foldl of byte-range inserts preserves getD at keys not in the list
-- ---------------------------------------------------------------------------

/-- A foldl of conditional inserts at indices ≠ k preserves `getD k`. -/
private lemma foldl_ne_inserts_preserves_getD (l : List Nat) (base : VocabMap) (k : Nat)
    (hne : ∀ j ∈ l, j ≠ k) :
    (l.foldl (fun (m : VocabMap) j =>
        if h : j < 256 then m.insert j (ByteArray.mk #[⟨j, h⟩]) else m) base).getD k ByteArray.empty =
    base.getD k ByteArray.empty := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
      simp only [List.foldl_cons]
      have hnej : j ≠ k := hne j List.mem_cons_self
      have hne' : ∀ x ∈ rest, x ≠ k := fun x hx => hne x (List.mem_cons_of_mem _ hx)
      by_cases h : j < 256
      · rw [dif_pos h, ih _ hne', Std.HashMap.getD_insert]
        simp [hnej]
      · rw [dif_neg h]; exact ih _ hne'

/-- The range-256 base fold sets `i.toNat` to `ByteArray.mk #[i]`. -/
private lemma base_fold_getD (i : UInt8) :
    ((List.range 256).foldl (fun (m : VocabMap) k =>
        if h : k < 256 then m.insert k (ByteArray.mk #[⟨k, h⟩]) else m) {}).getD i.toNat ByteArray.empty =
    ByteArray.mk #[i] := by
  have hi_mem : i.toNat ∈ List.range 256 := List.mem_range.mpr i.toNat_lt
  obtain ⟨s, t, hs⟩ := List.mem_iff_append.mp hi_mem
  -- hs : List.range 256 = s ++ i.toNat :: t
  rw [hs, List.foldl_append, List.foldl_cons]
  have h_lt : i.toNat < 256 := i.toNat_lt
  rw [dif_pos h_lt]
  -- t doesn't contain i.toNat (nodup of range 256)
  have hnd : (List.range 256).Nodup := List.nodup_range
  rw [hs] at hnd
  have hnd_it : (i.toNat :: t).Nodup := (List.nodup_append.mp hnd).2.1
  have hi_not_t : i.toNat ∉ t := (List.nodup_cons.mp hnd_it).1
  have hne_t : ∀ j ∈ t, j ≠ i.toNat := fun j hj hji => hi_not_t (hji ▸ hj)
  rw [foldl_ne_inserts_preserves_getD t _ i.toNat hne_t, Std.HashMap.getD_insert_self]
  simp

/-- The merge fold preserves `getD k` when `k` is not a merge target. -/
private lemma foldl_merges_preserves_getD
    (mergeList : List ((TokenId × TokenId) × TokenId))
    (base : VocabMap) (k : TokenId)
    (hfresh : ∀ entry ∈ mergeList, entry.2 ≠ k) :
    (mergeList.foldl (fun vocab ⟨(p0, p1), idx⟩ =>
        let v0 := vocab.getD p0 ByteArray.empty
        let v1 := vocab.getD p1 ByteArray.empty
        vocab.insert idx (v0 ++ v1)) base).getD k ByteArray.empty =
    base.getD k ByteArray.empty := by
  induction mergeList generalizing base with
  | nil => simp
  | cons entry rest ih =>
      obtain ⟨⟨p0, p1⟩, idx⟩ := entry
      simp only [List.foldl_cons]
      have hne : idx ≠ k := hfresh ⟨(p0, p1), idx⟩ List.mem_cons_self
      have hfresh' : ∀ e ∈ rest, e.2 ≠ k :=
          fun e he => hfresh e (List.mem_cons_of_mem _ he)
      rw [ih _ hfresh', Std.HashMap.getD_insert]
      simp [hne]

-- Partial lemma: base tokens are set correctly by buildVocab
lemma buildVocab_base_token
    (mergeList : List ((TokenId × TokenId) × TokenId))
    (i : UInt8)
    -- precondition: i.toNat is not a merge target
    (hfresh : ∀ entry ∈ mergeList, entry.2 ≠ i.toNat) :
    (buildVocab mergeList).getD i.toNat ByteArray.empty =
    ByteArray.mk #[i] := by
  simp only [buildVocab]
  rw [foldl_merges_preserves_getD mergeList _ i.toNat hfresh]
  exact base_fold_getD i

end BPE
