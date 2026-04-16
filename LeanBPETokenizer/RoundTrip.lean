import LeanBPETokenizer.EncDec

/-!
# Part 9 – Main Roundtrip Theorem

**Main Theorem**:
  ∀ s : ASCIIString,
    WellFormed(merges, vocab, byteShuffle) →
    inverseShuffle ∘ byteShuffle = id →
      decode vocab inverseShuffle (encode merges vocab byteShuffle s) = s

Proof chain:
  s
    ─[Lemma 7: UTF-8 encode]─►  text_bytes      (identity for ASCII)
    ─[Lemma 4: pre_tokenize]─►  chunks           (partition of text_bytes)
    ─[Lemma 1: BPE merges]──►  ids per chunk    (merge preservation)
    ─[Lemma 6: concat]───────►  all_ids          (decode_bytes distributes)
    ─[Lemma 2: unshuffle]────►  text_bytes       (shuffle cancellation)
    ─[Lemma 7: UTF-8 decode]─►  s                (identity for ASCII)
-/

namespace BPE

-- Lemma 7 is proved in EncDec.lean (lemma7_ascii_utf8_roundtrip).
-- (For ASCII strings, String.fromUTF8! ∘ String.toUTF8 = id.)

-- ---------------------------------------------------------------------------
-- Full roundtrip theorem
-- ---------------------------------------------------------------------------

/--
**Main Theorem** (ascii_bpe_roundtrip):

  ∀ s : ASCIIString,
    WellFormed merges vocab byteShuffle →
    (∀ b : UInt8, inverseShuffle (byteShuffle b) = b) →
      decode vocab inverseShuffle (encode merges vocab byteShuffle s) = s

**Proof structure**:

1. (Lemma 7) `s.toUTF8` gives bytes `text_bytes` with `text_bytes.decode = s`.

2. (Lemma 4) `preTokenizeASCII text_bytes = chunks` with `chunks.join = text_bytes`.

3. For each `chunk ∈ chunks`:
   - `shuffled_chunk = chunk.map byteShuffle`
   - `encode_chunk` starts with `ids_0 = shuffled_chunk.bytes` and applies merges.
   - By Lemma 1 (iterated): `decodeBytes vocab ids_final = shuffled_chunk`.

4. (Lemma 6) `decodeBytes vocab all_ids = all_shuffled` where
   `all_shuffled = text_bytes.map byteShuffle`.

5. (Lemma 2) `all_shuffled.map inverseShuffle = text_bytes`
   (pointwise shuffle cancellation).

6. (Lemma 7) `text_bytes.decode = s`.
-/
theorem ascii_bpe_roundtrip
    (merges         : MergeMap)
    (vocab          : VocabMap)
    (byteShuffle    : ByteShuffle)
    (inverseShuffle : ByteShuffle)
    (hw             : WellFormed merges vocab byteShuffle)
    (hinv           : ∀ b : UInt8, inverseShuffle (byteShuffle b) = b)
    (s              : String)
    (hascii         : ∀ c ∈ s.toList, c.val < 128) :
    decode vocab inverseShuffle (encode merges vocab byteShuffle s) = s := by
  simp only [decode, encode, decodeChunk]
  -- List foldl with arbitrary init
  have list_foldl_acc : ∀ (l : List ByteArray) (init : ByteArray),
      l.foldl (· ++ ·) init = init ++ l.foldl (· ++ ·) ByteArray.empty := by
    intro l; induction l with
    | nil => intro init; simp
    | cons h t ih =>
        intro init
        simp only [List.foldl_cons, ByteArray.empty_append]
        rw [ih (init ++ h), ih h, ByteArray.append_assoc]
  -- decodeChunk distributes over list append
  have dc_append : ∀ ids1 ids2 : List TokenId,
      ByteArray.mk ((decodeBytes vocab (ids1 ++ ids2)).data.map inverseShuffle) =
      ByteArray.mk ((decodeBytes vocab ids1).data.map inverseShuffle) ++
      ByteArray.mk ((decodeBytes vocab ids2).data.map inverseShuffle) := by
    intro ids1 ids2
    rw [decodeBytes_append]
    apply ByteArray.ext_iff.mpr
    simp [ByteArray.data_append, Array.map_append]
  -- decodeChunk over flatMap = foldl join (via chunkRoundtrip)
  have dc_flatmap : ∀ (l : List ByteArray),
      ByteArray.mk ((decodeBytes vocab (l.flatMap (encodeChunk merges vocab byteShuffle))).data.map inverseShuffle) =
      l.foldl (· ++ ·) ByteArray.empty := by
    intro l
    induction l with
    | nil => simp only [List.flatMap_nil, List.foldl_nil, decodeBytes_nil,
                        show (ByteArray.empty : ByteArray).data = #[] from rfl, Array.map_empty,
                        show ByteArray.mk #[] = ByteArray.empty from rfl]
    | cons c cs ih =>
        simp only [List.flatMap_cons]
        rw [dc_append, ih]
        have hcr : ByteArray.mk ((decodeBytes vocab (encodeChunk merges vocab byteShuffle c)).data.map inverseShuffle) = c :=
          chunkRoundtrip merges vocab byteShuffle inverseShuffle c hw.toEncodeReady hinv
        rw [hcr]
        simp only [List.foldl_cons, ByteArray.empty_append]
        rw [list_foldl_acc cs c]
  rw [dc_flatmap]
  -- Chunks join back to s.toUTF8 (Lemma 4)
  have h_part : (preTokenizeASCII s.toUTF8).toList.foldl (· ++ ·) ByteArray.empty = s.toUTF8 := by
    rw [Array.foldl_toList]
    exact preTokenize_partition s.toUTF8
  rw [h_part]
  -- UTF-8 roundtrip (Lemma 7)
  exact lemma7_ascii_utf8_roundtrip s hascii

/--
Operational roundtrip theorem: the proof only needs the `EncodeReady` subset
of the full `WellFormed` structure.
-/
theorem ascii_bpe_roundtrip_of_encodeReady
    (merges : MergeMap)
    (vocab : VocabMap)
    (byteShuffle inverseShuffle : ByteShuffle)
    (hw : EncodeReady merges vocab)
    (hinv : ∀ b : UInt8, inverseShuffle (byteShuffle b) = b)
    (s : String)
    (hascii : ∀ c ∈ s.toList, c.val < 128) :
    decode vocab inverseShuffle (encode merges vocab byteShuffle s) = s := by
  simp only [decode, encode, decodeChunk]
  have list_foldl_acc : ∀ (l : List ByteArray) (init : ByteArray),
      l.foldl (· ++ ·) init = init ++ l.foldl (· ++ ·) ByteArray.empty := by
    intro l; induction l with
    | nil => intro init; simp
    | cons h t ih =>
        intro init
        simp only [List.foldl_cons, ByteArray.empty_append]
        rw [ih (init ++ h), ih h, ByteArray.append_assoc]
  have dc_append : ∀ ids1 ids2 : List TokenId,
      ByteArray.mk ((decodeBytes vocab (ids1 ++ ids2)).data.map inverseShuffle) =
      ByteArray.mk ((decodeBytes vocab ids1).data.map inverseShuffle) ++
      ByteArray.mk ((decodeBytes vocab ids2).data.map inverseShuffle) := by
    intro ids1 ids2
    rw [decodeBytes_append]
    apply ByteArray.ext_iff.mpr
    simp [ByteArray.data_append, Array.map_append]
  have dc_flatmap : ∀ (l : List ByteArray),
      ByteArray.mk ((decodeBytes vocab (l.flatMap (encodeChunk merges vocab byteShuffle))).data.map inverseShuffle) =
      l.foldl (· ++ ·) ByteArray.empty := by
    intro l
    induction l with
    | nil => simp only [List.flatMap_nil, List.foldl_nil, decodeBytes_nil,
                        show (ByteArray.empty : ByteArray).data = #[] from rfl, Array.map_empty,
                        show ByteArray.mk #[] = ByteArray.empty from rfl]
    | cons c cs ih =>
        simp only [List.flatMap_cons]
        rw [dc_append, ih]
        have hcr : ByteArray.mk ((decodeBytes vocab (encodeChunk merges vocab byteShuffle c)).data.map inverseShuffle) = c :=
          chunkRoundtrip merges vocab byteShuffle inverseShuffle c hw hinv
        rw [hcr]
        simp only [List.foldl_cons, ByteArray.empty_append]
        rw [list_foldl_acc cs c]
  rw [dc_flatmap]
  have h_part : (preTokenizeASCII s.toUTF8).toList.foldl (· ++ ·) ByteArray.empty = s.toUTF8 := by
    rw [Array.foldl_toList]
    exact preTokenize_partition s.toUTF8
  rw [h_part]
  exact lemma7_ascii_utf8_roundtrip s hascii

/--
Construction-facing roundtrip theorem: validity handles the base-token part,
and callers can supply the remaining merge-decomposition proof for the built
merge map.
-/
theorem ascii_bpe_roundtrip_of_valid
    (mergeList : List MergeEntry)
    (hvalid : ValidMergeList mergeList)
    (byteShuffle inverseShuffle : ByteShuffle)
    (hinv : ∀ b : UInt8, inverseShuffle (byteShuffle b) = b)
    (s : String)
    (hascii : ∀ c ∈ s.toList, c.val < 128) :
    decode (buildVocab mergeList) inverseShuffle
      (encode (buildMerges mergeList) (buildVocab mergeList) byteShuffle s) = s :=
  ascii_bpe_roundtrip_of_encodeReady
    (buildMerges mergeList) (buildVocab mergeList) byteShuffle inverseShuffle
    (buildEncodeReady mergeList hvalid) hinv s hascii

end BPE
