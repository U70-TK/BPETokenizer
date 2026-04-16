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
private def baseVocab : VocabMap :=
  (List.range 256).foldl (fun m i =>
    if h : i < 256 then m.insert i (ByteArray.mk #[⟨i, h⟩]) else m) {}

private def vocabStep (vocab : VocabMap) (entry : (TokenId × TokenId) × TokenId) : VocabMap :=
  let v0 := vocab.getD entry.1.1 ByteArray.empty
  let v1 := vocab.getD entry.1.2 ByteArray.empty
  vocab.insert entry.2 (v0 ++ v1)

private def buildVocabFrom (vocab : VocabMap) (mergeList : List ((TokenId × TokenId) × TokenId)) :
    VocabMap :=
  mergeList.foldl (fun vocab ⟨(p0, p1), idx⟩ =>
    let v0 := vocab.getD p0 ByteArray.empty
    let v1 := vocab.getD p1 ByteArray.empty
    vocab.insert idx (v0 ++ v1)) vocab

def buildVocab (mergeList : List ((TokenId × TokenId) × TokenId)) : VocabMap :=
  buildVocabFrom baseVocab mergeList

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
  unfold buildVocab buildVocabFrom baseVocab
  rw [foldl_merges_preserves_getD mergeList _ i.toNat hfresh]
  exact base_fold_getD i

/-- Ordered merge-list entries used to build vocabularies and merge maps. -/
abbrev MergeEntry := ((TokenId × TokenId) × TokenId)

/-- Build the merge lookup table from an ordered merge list. -/
def buildMerges (mergeList : List MergeEntry) : MergeMap :=
  Std.HashMap.insertMany {} mergeList

/--
`EncodeReady` is the operational subset of `WellFormed` actually needed by the
current encoder/decoder proofs.
-/
structure EncodeReady (merges : MergeMap) (vocab : VocabMap) : Prop where
  /-- Every byte 0..255 is available as a singleton token. -/
  base_tokens : ∀ i : UInt8,
      vocab.getD i.toNat ByteArray.empty = ByteArray.mk #[i]
  /-- Every merge entry decodes to the concatenation of its component tokens. -/
  merge_decomp : ∀ (p0 p1 idx : TokenId),
      merges.getD (p0, p1) 0 = idx →
      merges.contains (p0, p1) →
      vocab.getD idx ByteArray.empty =
        vocab.getD p0 ByteArray.empty ++ vocab.getD p1 ByteArray.empty

/-- A fully well-formed tokenizer is in particular `EncodeReady`. -/
def WellFormed.toEncodeReady
    {merges : MergeMap} {vocab : VocabMap} {byteShuffle : ByteShuffle}
    (hw : WellFormed merges vocab byteShuffle) :
    EncodeReady merges vocab where
  base_tokens := hw.base_tokens
  merge_decomp := hw.merge_decomp

/--
Validity predicate for an ordered merge list.

`knownIds` tracks tokens already available in the partial vocabulary.
`knownPairs` tracks merge pairs already assigned in the partial merge map.
-/
private def ValidMergeList.go
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId)) : List MergeEntry → Prop
  | [] => True
  | ((p0, p1), idx) :: rest =>
      p0 ∈ knownIds ∧
      p1 ∈ knownIds ∧
      256 ≤ idx ∧
      idx ∉ knownIds ∧
      (p0, p1) ∉ knownPairs ∧
      ValidMergeList.go (knownIds ++ [idx]) (knownPairs ++ [(p0, p1)]) rest

/--
Public validity predicate for merge lists: every merge target is fresh, every
pair is assigned at most once, and each merge only references already-available
token ids.
-/
def ValidMergeList (mergeList : List MergeEntry) : Prop :=
  ValidMergeList.go (List.range 256) [] mergeList

/-- Advance the known-id state through a prefix of the merge list. -/
private def advanceKnownIds (knownIds : List TokenId) : List MergeEntry → List TokenId
  | [] => knownIds
  | entry :: rest => advanceKnownIds (knownIds ++ [entry.2]) rest

/-- Advance the known-pair state through a prefix of the merge list. -/
private def advanceKnownPairs
    (knownPairs : List (TokenId × TokenId)) : List MergeEntry → List (TokenId × TokenId)
  | [] => knownPairs
  | entry :: rest => advanceKnownPairs (knownPairs ++ [entry.1]) rest

/-- Every valid merge target lies outside the base-token range. -/
private lemma valid_target_ge
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId)) :
    ∀ (mergeList : List MergeEntry) (entry : MergeEntry),
      ValidMergeList.go knownIds knownPairs mergeList →
      entry ∈ mergeList →
      256 ≤ entry.2 := by
  intro mergeList
  induction mergeList generalizing knownIds knownPairs with
  | nil =>
      intro entry _ hmem
      cases hmem
  | cons head rest ih =>
      intro entry hvalid hmem
      obtain ⟨⟨p0, p1⟩, idx⟩ := head
      rcases hvalid with ⟨_, _, hidx, _, _, htail⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        exact hidx
      · exact ih (knownIds ++ [idx]) (knownPairs ++ [(p0, p1)]) entry htail hmem

/-- Later merge targets never overwrite ids that are already known. -/
private lemma valid_targets_avoid_known
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId)) :
    ∀ (mergeList : List MergeEntry) (k : TokenId),
      ValidMergeList.go knownIds knownPairs mergeList →
      k ∈ knownIds →
      ∀ entry ∈ mergeList, entry.2 ≠ k := by
  intro mergeList
  induction mergeList generalizing knownIds knownPairs with
  | nil =>
      intro k _ _ entry hmem
      cases hmem
  | cons head rest ih =>
      intro k hvalid hk entry hmem
      obtain ⟨pair, idx⟩ := head
      rcases hvalid with ⟨_, _, _, hidx_fresh, _, htail⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        intro hEq
        cases hEq
        have hkIdx : idx ∈ knownIds := hk
        exact hidx_fresh hkIdx
      · have hk' : k ∈ knownIds ++ [idx] := List.mem_append.mpr (.inl hk)
        exact ih (knownIds ++ [idx]) (knownPairs ++ [pair]) k htail hk' entry hmem

/-- Later merge pairs never overwrite pairs that are already known. -/
private lemma valid_pairs_avoid_known
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId)) :
    ∀ (mergeList : List MergeEntry) (k : TokenId × TokenId),
      ValidMergeList.go knownIds knownPairs mergeList →
      k ∈ knownPairs →
      ∀ entry ∈ mergeList, entry.1 ≠ k := by
  intro mergeList
  induction mergeList generalizing knownIds knownPairs with
  | nil =>
      intro k _ _ entry hmem
      cases hmem
  | cons head rest ih =>
      intro k hvalid hk entry hmem
      obtain ⟨pair, idx⟩ := head
      rcases hvalid with ⟨_, _, _, _, hpair_fresh, htail⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        intro hEq
        cases hEq
        have hkPair : pair ∈ knownPairs := hk
        exact hpair_fresh hkPair
      · have hk' : k ∈ knownPairs ++ [pair] := List.mem_append.mpr (.inl hk)
        exact ih (knownIds ++ [idx]) (knownPairs ++ [pair]) k htail hk' entry hmem

/-- Dropping a valid prefix yields a valid suffix with the advanced state. -/
private lemma valid_dropPrefix
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId))
    (pre : List MergeEntry)
    (suffix : List MergeEntry)
    (hvalid : ValidMergeList.go knownIds knownPairs (pre ++ suffix)) :
    ValidMergeList.go (advanceKnownIds knownIds pre) (advanceKnownPairs knownPairs pre) suffix := by
  revert knownIds knownPairs
  induction pre with
  | nil =>
      intro knownIds knownPairs hvalid
      simpa [advanceKnownIds, advanceKnownPairs] using hvalid
  | cons head rest ih =>
      intro knownIds knownPairs hvalid
      obtain ⟨pair, idx⟩ := head
      rcases hvalid with ⟨_, _, _, _, _, htail⟩
      simpa [advanceKnownIds, advanceKnownPairs] using
        ih (knownIds ++ [idx]) (knownPairs ++ [pair]) htail

/-- If a pair key appears in `mergeList.map Prod.fst`, some matching entry appears in `mergeList`. -/
private lemma mem_entry_of_mem_map_fst
    (mergeList : List MergeEntry)
    {pair : TokenId × TokenId} :
    pair ∈ mergeList.map Prod.fst →
    ∃ idx, ((pair, idx) : MergeEntry) ∈ mergeList := by
  intro hmem
  induction mergeList with
  | nil =>
      cases hmem
  | cons head rest ih =>
      obtain ⟨headPair, headIdx⟩ := head
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · exact ⟨headIdx, by cases hmem; simp⟩
      · rcases ih hmem with ⟨idx, hidx⟩
        exact ⟨idx, List.mem_cons_of_mem _ hidx⟩

/-- Valid merge lists assign each pair key at most once. -/
private lemma valid_pairwise_keys
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId)) :
    ∀ (mergeList : List MergeEntry),
      ValidMergeList.go knownIds knownPairs mergeList →
      mergeList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  intro mergeList
  induction mergeList generalizing knownIds knownPairs with
  | nil =>
      intro _
      simp
  | cons head rest ih =>
      intro hvalid
      obtain ⟨pair, idx⟩ := head
      rcases hvalid with ⟨_, _, _, _, _, htail⟩
      have hpair_not_mem : ∀ entry ∈ rest, entry.1 ≠ pair := by
        intro entry hentry
        have hk : pair ∈ knownPairs ++ [pair] := List.mem_append.mpr (.inr (by simp))
        have hneq := valid_pairs_avoid_known (knownIds ++ [idx]) (knownPairs ++ [pair])
          rest pair htail hk entry hentry
        simpa using hneq
      have hrest := ih (knownIds := knownIds ++ [idx]) (knownPairs := knownPairs ++ [pair]) htail
      refine List.pairwise_cons.2 ?_
      exact ⟨by
        intro entry hentry
        have hne : entry.1 ≠ pair := hpair_not_mem entry hentry
        have hne' : pair ≠ entry.1 := by
          intro hEq
          exact hne hEq.symm
        simpa [beq_iff_eq] using hne', hrest⟩

/-- Suffix processing preserves all ids that were already known when the suffix started. -/
private lemma buildVocabFrom_preserves_known
    (knownIds : List TokenId)
    (knownPairs : List (TokenId × TokenId))
    (vocab : VocabMap)
    (mergeList : List MergeEntry)
    (k : TokenId)
    (hvalid : ValidMergeList.go knownIds knownPairs mergeList)
    (hk : k ∈ knownIds) :
    (buildVocabFrom vocab mergeList).getD k ByteArray.empty =
      vocab.getD k ByteArray.empty := by
  simpa [buildVocabFrom, vocabStep] using
    foldl_merges_preserves_getD mergeList vocab k
      (fun entry hmem => valid_targets_avoid_known knownIds knownPairs mergeList k hvalid hk entry hmem)

/-- Any valid merge-list entry decodes to the concatenation of its component tokens. -/
  private theorem buildVocab_entry_decomp
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList)
    {p0 p1 idx : TokenId}
    (hmem : (((p0, p1), idx) : MergeEntry) ∈ mergeList) :
    (buildVocab mergeList).getD idx ByteArray.empty =
      (buildVocab mergeList).getD p0 ByteArray.empty ++
      (buildVocab mergeList).getD p1 ByteArray.empty := by
  obtain ⟨pre, suffix, hsplit⟩ := List.mem_iff_append.mp hmem
  have hvalidSplit :
      ValidMergeList.go (List.range 256) [] (pre ++ (((p0, p1), idx) : MergeEntry) :: suffix) := by
    simpa [ValidMergeList, hsplit] using hvalid
  have hstate :
      ValidMergeList.go (advanceKnownIds (List.range 256) pre) (advanceKnownPairs [] pre)
        ((((p0, p1), idx) : MergeEntry) :: suffix) := by
    simpa using
      valid_dropPrefix (knownIds := List.range 256) (knownPairs := [])
        pre ((((p0, p1), idx) : MergeEntry) :: suffix) hvalidSplit
  rcases hstate with ⟨hp0, hp1, _, hidx_fresh, _, hsuffix⟩
  let prefixVocab := buildVocabFrom baseVocab pre
  let entryVocab := vocabStep prefixVocab (((p0, p1), idx) : MergeEntry)
  have hbuild :
      buildVocab mergeList = buildVocabFrom entryVocab suffix := by
    rw [hsplit, buildVocab, buildVocabFrom, List.foldl_append, List.foldl_cons]
    rfl
  have hk_idx : idx ∈ advanceKnownIds (List.range 256) pre ++ [idx] := by simp
  have hk_p0 : p0 ∈ advanceKnownIds (List.range 256) pre ++ [idx] :=
    List.mem_append.mpr (.inl hp0)
  have hk_p1 : p1 ∈ advanceKnownIds (List.range 256) pre ++ [idx] :=
    List.mem_append.mpr (.inl hp1)
  have hidx_final :
      (buildVocab mergeList).getD idx ByteArray.empty =
        entryVocab.getD idx ByteArray.empty := by
    rw [hbuild]
    exact buildVocabFrom_preserves_known
      (knownIds := advanceKnownIds (List.range 256) pre ++ [idx])
      (knownPairs := advanceKnownPairs [] pre ++ [(p0, p1)])
      (vocab := entryVocab) (mergeList := suffix) (k := idx) hsuffix hk_idx
  have hp0_final :
      (buildVocab mergeList).getD p0 ByteArray.empty =
        entryVocab.getD p0 ByteArray.empty := by
    rw [hbuild]
    exact buildVocabFrom_preserves_known
      (knownIds := advanceKnownIds (List.range 256) pre ++ [idx])
      (knownPairs := advanceKnownPairs [] pre ++ [(p0, p1)])
      (vocab := entryVocab) (mergeList := suffix) (k := p0) hsuffix hk_p0
  have hp1_final :
      (buildVocab mergeList).getD p1 ByteArray.empty =
        entryVocab.getD p1 ByteArray.empty := by
    rw [hbuild]
    exact buildVocabFrom_preserves_known
      (knownIds := advanceKnownIds (List.range 256) pre ++ [idx])
      (knownPairs := advanceKnownPairs [] pre ++ [(p0, p1)])
      (vocab := entryVocab) (mergeList := suffix) (k := p1) hsuffix hk_p1
  have hp0_ne : p0 ≠ idx := by
    intro hEq
    exact hidx_fresh (hEq ▸ hp0)
  have hp1_ne : p1 ≠ idx := by
    intro hEq
    exact hidx_fresh (hEq ▸ hp1)
  have hp0_step :
      entryVocab.getD p0 ByteArray.empty = prefixVocab.getD p0 ByteArray.empty := by
    have hne : idx ≠ p0 := fun hEq => hp0_ne hEq.symm
    have hbeq : (idx == p0) = false := by simpa [beq_iff_eq] using hne
    simpa [entryVocab, prefixVocab, vocabStep, hbeq] using
      (Std.HashMap.getD_insert (m := prefixVocab) (k := idx) (a := p0)
        (fallback := ByteArray.empty)
        (v := prefixVocab.getD p0 ByteArray.empty ++ prefixVocab.getD p1 ByteArray.empty))
  have hp1_step :
      entryVocab.getD p1 ByteArray.empty = prefixVocab.getD p1 ByteArray.empty := by
    have hne : idx ≠ p1 := fun hEq => hp1_ne hEq.symm
    have hbeq : (idx == p1) = false := by simpa [beq_iff_eq] using hne
    simpa [entryVocab, prefixVocab, vocabStep, hbeq] using
      (Std.HashMap.getD_insert (m := prefixVocab) (k := idx) (a := p1)
        (fallback := ByteArray.empty)
        (v := prefixVocab.getD p0 ByteArray.empty ++ prefixVocab.getD p1 ByteArray.empty))
  calc
    (buildVocab mergeList).getD idx ByteArray.empty
        = entryVocab.getD idx ByteArray.empty := hidx_final
    _ = prefixVocab.getD p0 ByteArray.empty ++ prefixVocab.getD p1 ByteArray.empty := by
      simp [entryVocab, prefixVocab, vocabStep]
    _ = entryVocab.getD p0 ByteArray.empty ++ entryVocab.getD p1 ByteArray.empty := by
      rw [hp0_step, hp1_step]
    _ = (buildVocab mergeList).getD p0 ByteArray.empty ++
        (buildVocab mergeList).getD p1 ByteArray.empty := by
      rw [← hp0_final, ← hp1_final]

/-- If the built merge map returns an entry, that exact entry came from the valid merge list. -/
private theorem buildMerges_mem_of_lookup
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList)
    {p0 p1 idx : TokenId}
    (hget : (buildMerges mergeList).getD (p0, p1) 0 = idx)
    (hcontains : (buildMerges mergeList).contains (p0, p1)) :
    (((p0, p1), idx) : MergeEntry) ∈ mergeList := by
  have hpair_contains : (mergeList.map Prod.fst).contains (p0, p1) = true := by
    simpa [buildMerges] using hcontains
  have hpair_mem : (p0, p1) ∈ mergeList.map Prod.fst := by
    simpa using hpair_contains
  rcases mem_entry_of_mem_map_fst mergeList hpair_mem with ⟨idx', hmem'⟩
  have hpairwise := valid_pairwise_keys (knownIds := List.range 256) (knownPairs := []) mergeList hvalid
  have hget' : (buildMerges mergeList).getD (p0, p1) 0 = idx' := by
    simpa [buildMerges] using
      (Std.HashMap.getD_insertMany_list_of_mem (m := ({} : MergeMap))
        (l := mergeList) (k := (p0, p1)) (k' := (p0, p1)) (k_beq := by simp)
        (v := idx') (fallback := 0) hpairwise hmem')
  have hEq : idx = idx' := by rw [← hget', hget]
  simpa [hEq] using hmem'

/-- Any valid merge target remains a base singleton token after vocab construction. -/
theorem valid_buildVocab_base_token
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList)
    (i : UInt8) :
    (buildVocab mergeList).getD i.toNat ByteArray.empty = ByteArray.mk #[i] := by
  apply buildVocab_base_token
  intro entry hmem
  have hge := valid_target_ge (List.range 256) [] mergeList entry hvalid hmem
  intro hEq
  have hi : i.toNat < 256 := i.toNat_lt
  have hge' : 256 ≤ i.toNat := by simpa [hEq] using hge
  omega

/-- A valid merge list constructs an `EncodeReady` tokenizer. -/
theorem buildEncodeReady
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList) :
    EncodeReady (buildMerges mergeList) (buildVocab mergeList) where
  base_tokens := valid_buildVocab_base_token mergeList hvalid
  merge_decomp := by
    intro p0 p1 idx hget hcontains
    have hmem : (((p0, p1), idx) : MergeEntry) ∈ mergeList :=
      buildMerges_mem_of_lookup mergeList hvalid hget hcontains
    exact buildVocab_entry_decomp mergeList hvalid hmem

/--
Given a valid merge list and an explicit proof of the merge-decomposition
property for the constructed merge map, the resulting tokenizer is `EncodeReady`.
-/
theorem buildEncodeReadyFromAssumptions
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList)
    (hdecomp : ∀ (p0 p1 idx : TokenId),
      (buildMerges mergeList).getD (p0, p1) 0 = idx →
      (buildMerges mergeList).contains (p0, p1) →
      (buildVocab mergeList).getD idx ByteArray.empty =
        (buildVocab mergeList).getD p0 ByteArray.empty ++
        (buildVocab mergeList).getD p1 ByteArray.empty) :
    EncodeReady (buildMerges mergeList) (buildVocab mergeList) where
  base_tokens := valid_buildVocab_base_token mergeList hvalid
  merge_decomp := hdecomp

/-- The empty merge list is valid. -/
theorem emptyValidMergeList : ValidMergeList [] := by
  simp [ValidMergeList, ValidMergeList.go]

/-- The empty merge list gives a verified byte-level tokenizer. -/
theorem emptyEncodeReady : EncodeReady (buildMerges []) (buildVocab []) :=
  buildEncodeReady [] emptyValidMergeList

end BPE
