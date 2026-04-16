import LeanBPETokenizer.WellFormed
import LeanBPETokenizer.PreTokenizer

/-!
# Part 6 – Encode and Decode

Implements `encodeChunk`, `decodeChunk`, `encode`, and `decode`,
mirroring Parts 6–7 of `core.py`.

Key invariants maintained throughout encoding:
  `decodeBytes vocab ids = shuffled`
where `shuffled = token_bytes.map byteShuffle`.

These invariants, combined with Lemma 1 (merge preservation) and
Lemma 2 (shuffle cancellation), yield the per-chunk roundtrip:
  `decodeChunk (encodeChunk chunk) = chunk`
-/

namespace BPE

-- ---------------------------------------------------------------------------
-- encodeChunkLoop (fuel-based merge loop, termination by fuel)
-- ---------------------------------------------------------------------------

/--
Fuel-based BPE merge loop.  Terminates trivially because `fuel` decreases.
Passing `ids.length` as fuel is sufficient: each merge strictly reduces the
list length (by `bpeMerge_length_lt`), so at most that many merges occur.
-/
private def encodeChunkLoop (merges : MergeMap) : Nat → List TokenId → List TokenId
  | 0,        ids => ids
  | fuel + 1, ids =>
      if ids.length < 2 then ids
      else
        let stats := getStats ids
        let candidates : List (TokenId × TokenId × TokenId) :=
          stats.toList.filterMap (fun ⟨pair, _⟩ =>
            match merges.get? pair with
            | none     => none
            | some idx => some (pair.1, pair.2, idx))
        match candidates with
        | [] => ids
        | _ =>
            let best := candidates.foldl (fun acc ⟨p0, p1, idx⟩ =>
              match acc with
              | none              => some (p0, p1, idx)
              | some ⟨_, _, bIdx⟩ => if idx < bIdx then some (p0, p1, idx) else acc)
              (none : Option (TokenId × TokenId × TokenId))
            match best with
            | none              => ids
            | some ⟨p0, p1, idx⟩ => encodeChunkLoop merges fuel (bpeMerge ids (p0, p1) idx)

-- ---------------------------------------------------------------------------
-- encodeChunk
-- ---------------------------------------------------------------------------

/--
BPE-encode a single pre-tokenized chunk of bytes into a list of token ids.

Steps:
1. Apply `byteShuffle` to every byte.
2. Start with each shuffled byte as its own singleton token id.
3. Repeatedly find the lowest-ranked adjacent pair in the current id list
   and merge it, until no more merges are possible.

**Invariant** (maintained by Lemma 1 at every merge step):
  `decodeBytes vocab ids = shuffledBytes`
-/
def encodeChunk
    (merges      : MergeMap)
    (vocab       : VocabMap)
    (byteShuffle : ByteShuffle)
    (textBytes   : ByteArray) : List TokenId :=
  -- Step 1: shuffle bytes
  let shuffled : ByteArray := ByteArray.mk (textBytes.data.map byteShuffle)
  -- Step 2: initialise ids = list of single-byte token ids
  let ids₀ : List TokenId := shuffled.data.toList.map (·.toNat)
  -- Step 3: merge loop (fuel = ids₀.length suffices: each merge shrinks the list)
  encodeChunkLoop merges ids₀.length ids₀

-- ---------------------------------------------------------------------------
-- decodeChunk
-- ---------------------------------------------------------------------------

/--
Decode a list of token ids back to the original raw bytes.

1. Concatenate vocab entries → recovers the shuffled bytes.
2. Apply `inverseShuffle` to every byte → recovers original bytes.
-/
def decodeChunk
    (vocab          : VocabMap)
    (inverseShuffle : ByteShuffle)
    (ids            : List TokenId) : ByteArray :=
  let raw := decodeBytes vocab ids
  ByteArray.mk (raw.data.map inverseShuffle)

-- ---------------------------------------------------------------------------
-- encode (full string)
-- ---------------------------------------------------------------------------

/--
Full encoding of an ASCII string to a list of token ids.

1. UTF-8 encode (identity for ASCII — Lemma 7).
2. Pre-tokenize using `preTokenizeASCII` (Lemma 4: partition).
3. Encode each chunk with `encodeChunk` (Lemma 1 per chunk).
-/
def encodeWithProfile
    (profile : PreTokenizerProfile)
    (merges      : MergeMap)
    (vocab       : VocabMap)
    (byteShuffle : ByteShuffle)
    (text        : String) : List TokenId :=
  let textBytes := text.toUTF8
  let chunks    := preTokenizeASCII profile textBytes
  chunks.toList.flatMap (fun chunk => encodeChunk merges vocab byteShuffle chunk)

/-- `cl100k`-style encoding retained as the default convenience wrapper. -/
def encode
    (merges      : MergeMap)
    (vocab       : VocabMap)
    (byteShuffle : ByteShuffle)
    (text        : String) : List TokenId :=
  encodeWithProfile .cl100k merges vocab byteShuffle text

-- ---------------------------------------------------------------------------
-- decode (full string)
-- ---------------------------------------------------------------------------

/--
Full decoding of a list of token ids to an ASCII string.

1. Decode all ids at once.
2. Apply `inverseShuffle` to each byte.
3. UTF-8 decode (identity for ASCII — Lemma 7).
-/
def decode
    (vocab          : VocabMap)
    (inverseShuffle : ByteShuffle)
    (ids            : List TokenId) : String :=
  let rawBytes := decodeChunk vocab inverseShuffle ids
  String.fromUTF8! rawBytes

-- ---------------------------------------------------------------------------
-- Lemma 7 – ASCII UTF-8 Roundtrip
-- ---------------------------------------------------------------------------

/--
**Lemma 7**: For any ASCII string `s`,
  `String.fromUTF8! (s.toUTF8) = s`.
-/
theorem lemma7_ascii_utf8_roundtrip (s : String)
    (hascii : ∀ c ∈ s.toList, c.val < 128) :
    String.fromUTF8! s.toUTF8 = s := by
  -- String is defined as `{ toByteArray : ByteArray, isValidUTF8 : ... }`.
  -- fromUTF8! s.toByteArray reduces to fromUTF8 s.toByteArray s.isValidUTF8 = s.
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8!,
             dif_pos s.isValidUTF8, String.fromUTF8]

-- ---------------------------------------------------------------------------
-- Helper lemmas for chunkRoundtrip
-- ---------------------------------------------------------------------------

/-- If `best = some (p0, p1, idx)` from the min-idx foldl on `candidates`,
    then `(p0, p1, idx) ∈ candidates`. -/
private lemma foldl_best_mem_candidates :
    ∀ (candidates : List (TokenId × TokenId × TokenId))
      (acc : Option (TokenId × TokenId × TokenId))
      (p0 p1 idx : TokenId),
    candidates.foldl (fun acc x =>
      match acc with
      | none => some (x.1, x.2.1, x.2.2)
      | some (_, _, bIdx) => if x.2.2 < bIdx then some (x.1, x.2.1, x.2.2) else acc)
    acc = some (p0, p1, idx) →
    (p0, p1, idx) ∈ candidates ∨ acc = some (p0, p1, idx) := by
  intro candidates
  induction candidates with
  | nil => intro acc p0 p1 idx h; simp at h; exact Or.inr h
  | cons head rest ih =>
      intro acc p0 p1 idx hfold
      simp only [List.foldl_cons] at hfold
      rcases ih _ p0 p1 idx hfold with hmem | hacc'
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · simp only [List.mem_cons]
        cases acc with
        | none =>
            simp only at hacc'
            simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
            obtain ⟨hp0, hp1, hidx⟩ := hacc'
            left; left
            apply Eq.symm; apply Prod.ext; exact hp0; exact Prod.ext hp1 hidx
        | some best =>
            simp only at hacc'
            split_ifs at hacc' with hlt
            · simp only [Option.some.injEq, Prod.mk.injEq] at hacc'
              obtain ⟨hp0, hp1, hidx⟩ := hacc'
              left; left
              apply Eq.symm; apply Prod.ext; exact hp0; exact Prod.ext hp1 hidx
            · exact Or.inr hacc'

/-- If `(p0, p1, idx) ∈ stats.toList.filterMap f` where `f` looks up in `merges`,
    then `merges.get? (p0, p1) = some idx`. -/
private lemma filterMap_mem_merges
    (merges : MergeMap)
    (stats : Std.HashMap (TokenId × TokenId) Nat)
    (p0 p1 idx : TokenId)
    (h : (p0, p1, idx) ∈ stats.toList.filterMap (fun (kv : (TokenId × TokenId) × Nat) =>
           match merges.get? kv.1 with
           | none     => none
           | some i   => some (kv.1.1, kv.1.2, i))) :
    merges.get? (p0, p1) = some idx := by
  rw [List.mem_filterMap] at h
  obtain ⟨⟨pair, _⟩, _, hfun⟩ := h
  simp only at hfun
  -- hfun : (match merges.get? pair with | none => none | some i => some (pair.1, pair.2, i))
  --           = some (p0, p1, idx)
  cases hm : merges.get? pair with
  | none =>
      rw [hm] at hfun
      simp at hfun
  | some mergeIdx =>
      rw [hm] at hfun
      simp only [Option.some.injEq, Prod.mk.injEq] at hfun
      obtain ⟨hp0, hp1, hidx⟩ := hfun
      rw [show (p0, p1) = pair from Prod.ext hp0.symm hp1.symm, ← hidx]
      exact hm

/-- `encodeChunkLoop` preserves `decodeBytes` under `WellFormed`. -/
private lemma encodeChunkLoop_decode_inv
    (merges : MergeMap) (vocab : VocabMap) (byteShuffle : ByteShuffle)
    (hw : EncodeReady merges vocab)
    (fuel : Nat) (ids : List TokenId) :
    decodeBytes vocab (encodeChunkLoop merges fuel ids) = decodeBytes vocab ids := by
  induction fuel generalizing ids with
  | zero => simp [encodeChunkLoop]
  | succ fuel ih =>
      simp only [encodeChunkLoop]
      split_ifs with hlt
      · rfl
      · -- The inner expression has let-bindings followed by match on candidates.
        -- We extract the key components by naming them.
        set cands := (getStats ids).toList.filterMap (fun kv =>
            match merges.get? kv.1 with
            | none => none
            | some i => some (kv.1.1, kv.1.2, i)) with h_cands
        -- Case split on cands
        rcases hcands : cands with _ | ⟨head, rest⟩
        · -- cands = [] → outer match iota-reduces to ids → goal is rfl
          simp only [hcands]
        · -- cands = head :: rest; outer match + let best reduced by simp
          simp only [hcands]
          -- Goal: decodeBytes vocab (match <foldl_expr> with | none => ids | some ⟨..⟩ => ..) = ..
          -- Case-split on the result of the foldl (the inner match scrutinee)
          split
          · -- foldl returned none → inner match → ids → rfl
            rfl
          · -- foldl returned some (p0, p1, idx)
            rename_i p0 p1 idx h_best
            -- h_best : <foldl_expr> = some (p0, p1, idx)
            rw [ih]
            apply bpeMerge_decode_eq
            -- (p0, p1, idx) ∈ head :: rest via foldl_best_mem_candidates
            have hmem : (p0, p1, idx) ∈ head :: rest := by
              rcases foldl_best_mem_candidates (head :: rest) none p0 p1 idx h_best with h | h
              · exact h
              · simp at h
            -- merges.get? (p0, p1) = some idx
            have hget : merges.get? (p0, p1) = some idx := by
              apply filterMap_mem_merges merges (getStats ids) p0 p1 idx
              rw [h_cands.symm.trans hcands]
              exact hmem
            have hcont : merges.contains (p0, p1) = true := by
              simp only [Std.HashMap.contains_eq_isSome_getElem?]
              rw [show merges[(p0, p1)]? = some idx from hget]
              rfl
            have hgetD : merges.getD (p0, p1) 0 = idx := by
              rw [Std.HashMap.getD_eq_getD_getElem?, show merges[(p0, p1)]? = some idx from hget]
              rfl
            exact hw.merge_decomp p0 p1 idx hgetD hcont

/-- `encodeChunkLoop` preserves any predicate that holds on the initial ids and
all merge targets. -/
private lemma encodeChunkLoop_preserves
    (merges : MergeMap)
    (P : TokenId → Prop)
    (hmerge : ∀ p0 p1 idx, merges.get? (p0, p1) = some idx → P idx)
    (fuel : Nat)
    (ids : List TokenId)
    (hids : ∀ id ∈ ids, P id) :
    ∀ id ∈ encodeChunkLoop merges fuel ids, P id := by
  induction fuel generalizing ids with
  | zero =>
      intro id hid
      simpa [encodeChunkLoop] using hids id hid
  | succ fuel ih =>
      simp only [encodeChunkLoop]
      split_ifs with hlt
      · intro id hid
        exact hids id hid
      · set cands := (getStats ids).toList.filterMap (fun kv =>
            match merges.get? kv.1 with
            | none => none
            | some i => some (kv.1.1, kv.1.2, i)) with h_cands
        rcases hcands : cands with _ | ⟨head, rest⟩
        · intro id hid
          simpa [hcands] using hids id hid
        · simp only [hcands]
          split
          · intro id hid
            exact hids id hid
          · rename_i p0 p1 idx h_best
            have hmem : (p0, p1, idx) ∈ head :: rest := by
              rcases foldl_best_mem_candidates (head :: rest) none p0 p1 idx h_best with h | h
              · exact h
              · simp at h
            have hget : merges.get? (p0, p1) = some idx := by
              apply filterMap_mem_merges merges (getStats ids) p0 p1 idx
              rw [h_cands.symm.trans hcands]
              exact hmem
            have hmergedIds : ∀ id ∈ bpeMerge ids (p0, p1) idx, P id :=
              bpeMerge_preserves P ids (p0, p1) idx (hmerge p0 p1 idx hget) hids
            exact ih (bpeMerge ids (p0, p1) idx) hmergedIds

/-- The initial single-byte id list decodes to the shuffled byte array. -/
private lemma ids0_decode_eq (vocab : VocabMap)
    (hbase : ∀ i : UInt8, vocab.getD i.toNat ByteArray.empty = ByteArray.mk #[i])
    (shuffled : ByteArray) :
    decodeBytes vocab (shuffled.data.toList.map (·.toNat)) = shuffled := by
  -- Reduce to: for any List UInt8 l, decoding the id list gives back ByteArray.mk l.toArray
  suffices h : ∀ (l : List UInt8),
      decodeBytes vocab (l.map (·.toNat)) = ByteArray.mk l.toArray by
    have := h shuffled.data.toList
    rwa [Array.toArray_toList] at this
  intro l
  induction l with
  | nil => rfl
  | cons b rest ih =>
      rw [List.map_cons,
          show b.toNat :: rest.map (·.toNat) = [b.toNat] ++ rest.map (·.toNat) from rfl,
          decodeBytes_append, decodeBytes_singleton, hbase, ih]
      -- Goal: ByteArray.mk #[b] ++ ByteArray.mk rest.toArray = ByteArray.mk (b :: rest).toArray
      apply ByteArray.ext_iff.mpr
      simp only [ByteArray.data_append]
      -- Goal: #[b] ++ rest.toArray = (b :: rest).toArray
      apply Array.ext'
      simp [Array.toList_append, List.toList_toArray]

-- ---------------------------------------------------------------------------
-- Per-chunk roundtrip
-- ---------------------------------------------------------------------------

/--
**Per-chunk roundtrip**: under `WellFormed` and shuffle inverse hypothesis,
`decodeChunk (encodeChunk chunk) = chunk`.
-/
theorem chunkRoundtrip
    (merges      : MergeMap)
    (vocab       : VocabMap)
    (byteShuffle inverseShuffle : ByteShuffle)
    (chunk       : ByteArray)
    (hw          : EncodeReady merges vocab)
    (hinv        : ∀ b : UInt8, inverseShuffle (byteShuffle b) = b) :
    decodeChunk vocab inverseShuffle
      (encodeChunk merges vocab byteShuffle chunk) = chunk := by
  simp only [decodeChunk, encodeChunk]
  set shuffled := ByteArray.mk (chunk.data.map byteShuffle) with h_shuffled
  set ids₀ := shuffled.data.toList.map (·.toNat) with h_ids₀
  -- Step 1: loop preserves decodeBytes
  rw [encodeChunkLoop_decode_inv merges vocab byteShuffle hw]
  -- Step 2: initial ids decode to shuffled
  rw [ids0_decode_eq vocab hw.base_tokens shuffled]
  -- Step 3: inverseShuffle recovers chunk
  -- Goal: ByteArray.mk ((ByteArray.mk (chunk.data.map byteShuffle)).data.map inverseShuffle) = chunk
  show ByteArray.mk ((chunk.data.map byteShuffle).map inverseShuffle) = chunk
  rw [Array.map_map]
  exact shuffle_cancel_array byteShuffle inverseShuffle hinv chunk

/-- Encoding a chunk preserves any token-id predicate that holds on shuffled
base-byte ids and every merge target. -/
theorem encodeChunk_preserves
    (merges : MergeMap)
    (vocab : VocabMap)
    (byteShuffle : ByteShuffle)
    (chunk : ByteArray)
    (P : TokenId → Prop)
    (hbase : ∀ b : UInt8, P b.toNat)
    (hmerge : ∀ p0 p1 idx, merges.get? (p0, p1) = some idx → P idx) :
    ∀ id ∈ encodeChunk merges vocab byteShuffle chunk, P id := by
  simp only [encodeChunk]
  set shuffled := ByteArray.mk (chunk.data.map byteShuffle)
  set ids₀ : List TokenId := shuffled.data.toList.map (·.toNat) with h_ids₀
  have hids₀ : ∀ id ∈ ids₀, P id := by
    intro id hid
    rw [h_ids₀] at hid
    rw [List.mem_map] at hid
    rcases hid with ⟨b, hb, rfl⟩
    exact hbase b
  exact encodeChunkLoop_preserves merges P hmerge ids₀.length ids₀ hids₀

/-- Full-string encoding preserves any token-id predicate that holds on
shuffled base-byte ids and every merge target. -/
theorem encodeWithProfile_preserves
    (profile : PreTokenizerProfile)
    (merges : MergeMap)
    (vocab : VocabMap)
    (byteShuffle : ByteShuffle)
    (text : String)
    (P : TokenId → Prop)
    (hbase : ∀ b : UInt8, P b.toNat)
    (hmerge : ∀ p0 p1 idx, merges.get? (p0, p1) = some idx → P idx) :
    ∀ id ∈ encodeWithProfile profile merges vocab byteShuffle text, P id := by
  intro id hid
  simp only [encodeWithProfile] at hid
  rw [List.mem_flatMap] at hid
  rcases hid with ⟨chunk, hchunk, hidChunk⟩
  exact encodeChunk_preserves merges vocab byteShuffle chunk P hbase hmerge id hidChunk

/-- Default `cl100k` wrapper for the preservation theorem. -/
theorem encode_preserves
    (merges : MergeMap)
    (vocab : VocabMap)
    (byteShuffle : ByteShuffle)
    (text : String)
    (P : TokenId → Prop)
    (hbase : ∀ b : UInt8, P b.toNat)
    (hmerge : ∀ p0 p1 idx, merges.get? (p0, p1) = some idx → P idx) :
    ∀ id ∈ encode merges vocab byteShuffle text, P id :=
  encodeWithProfile_preserves .cl100k merges vocab byteShuffle text P hbase hmerge

/-- Convenience wrapper from the stronger `WellFormed` hypothesis. -/
theorem chunkRoundtrip_of_wellFormed
    (merges : MergeMap)
    (vocab : VocabMap)
    (byteShuffle inverseShuffle : ByteShuffle)
    (chunk : ByteArray)
    (hw : WellFormed merges vocab byteShuffle)
    (hinv : ∀ b : UInt8, inverseShuffle (byteShuffle b) = b) :
    decodeChunk vocab inverseShuffle
      (encodeChunk merges vocab byteShuffle chunk) = chunk :=
  chunkRoundtrip merges vocab byteShuffle inverseShuffle chunk hw.toEncodeReady hinv

end BPE
