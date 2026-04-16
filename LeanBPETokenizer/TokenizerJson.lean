import LeanBPETokenizer.RoundTrip
import Lean.Data.Json.Parser
import Std.Data.HashMap.Lemmas

namespace BPE

open Lean

/-- Default tokenizer path used by the CLI. -/
def defaultTokenizerPath : System.FilePath := "tokenizers/o200k_harmony/tokenizer.json"

/-- Runtime tokenizer built from the ASCII-compatible subset of a GPT byte-level BPE JSON. -/
structure LoadedAsciiTokenizer where
  profile : PreTokenizerProfile
  merges : MergeMap
  vocab : VocabMap
  externalToInternal : Std.HashMap TokenId TokenId
  internalToExternal : Std.HashMap TokenId TokenId

private def cl100kSplitRegex : String :=
  "(?i:'s|'t|'re|'ve|'m|'ll|'d)|[^\\r\\n\\p{L}\\p{N}]?\\p{L}+|\\p{N}{1,3}| ?[^\\s\\p{L}\\p{N}]+[\\r\\n]*|\\s*[\\r\\n]+|\\s+(?!\\S)|\\s+"

private def o200kSplitRegex : String :=
  "[^\\r\\n\\p{L}\\p{N}]?[\\p{Lu}\\p{Lt}\\p{Lm}\\p{Lo}\\p{M}]*[\\p{Ll}\\p{Lm}\\p{Lo}\\p{M}]+(?i:'s|'t|'re|'ve|'m|'ll|'d)?|[^\\r\\n\\p{L}\\p{N}]?[\\p{Lu}\\p{Lt}\\p{Lm}\\p{Lo}\\p{M}]+[\\p{Ll}\\p{Lm}\\p{Lo}\\p{M}]*(?i:'s|'t|'re|'ve|'m|'ll|'d)?|\\p{N}{1,3}| ?[^\\s\\p{L}\\p{N}]+[\\r\\n/]*|\\s*[\\r\\n]+|\\s+(?!\\S)|\\s+"

private def visibleByteNats : List Nat :=
  (List.range (126 - 33 + 1)).map (· + 33) ++
  (List.range (172 - 161 + 1)).map (· + 161) ++
  (List.range (255 - 174 + 1)).map (· + 174)

private def gptByteToUnicodeTable : Array Char :=
  Id.run do
    let visibleSet : Std.HashSet Nat := visibleByteNats.foldl (fun s b => s.insert b) {}
    let mut pairs : Array (Nat × Char) := #[]
    for b in visibleByteNats do
      pairs := pairs.push (b, Char.ofNat b)
    let mut extra := 0
    for b in List.range 256 do
      if !visibleSet.contains b then
        pairs := pairs.push (b, Char.ofNat (256 + extra))
        extra := extra + 1
    let mut table := Array.replicate 256 (Char.ofNat 0)
    for pair in pairs do
      table := table.set! pair.1 pair.2
    table

private def gptCharToByte : Std.HashMap Char UInt8 :=
  (List.range 256).foldl (fun m n =>
    if h : n < 256 then
      let b : UInt8 := ⟨n, by omega⟩
      m.insert gptByteToUnicodeTable[n]! b
    else m) {}

private def decodeByteLevelToken (token : String) : Except String ByteArray := do
  let mut out := ByteArray.empty
  for c in token.toList do
    match gptCharToByte.get? c with
    | some b => out := out.push b
    | none => throw s!"unsupported tokenizer character {repr c} in token {repr token}"
  pure out

private def isAsciiBytes (bs : ByteArray) : Bool :=
  bs.data.all fun b => b.toNat < 128

private def isAsciiString (s : String) : Bool :=
  s.toList.all fun c => c.val < 128

private def parseVocab (j : Json) : Except String (Std.HashMap String TokenId) := do
  let obj <- j.getObj?
  pure <|
    obj.foldl (init := ({} : Std.HashMap String TokenId)) fun acc tok value =>
      match value.getNat? with
      | .ok id => acc.insert tok id
      | .error _ => acc

private def parseMerges (j : Json) : Except String (Array (String × String)) := do
  let arr <- j.getArr?
  let mut out := #[]
  for entry in arr do
    match entry with
    | .arr parts =>
        if h : parts.size = 2 then
          let left <- (parts[0]).getStr?
          let right <- (parts[1]).getStr?
          out := out.push (left, right)
        else
          throw s!"merge entry must have length 2, got {parts.size}"
    | .str pair =>
        match pair.splitOn " " with
        | [left, right] => out := out.push (left, right)
        | _ => throw s!"string merge entry must contain exactly one separator space: {repr pair}"
    | _ =>
        throw "merge entry must be either a 2-element array or a 'left right' string"
  pure out

private def parsePreTokenizerProfile (root : Json) : Except String PreTokenizerProfile := do
  let preTokenizer <- root.getObjVal? "pre_tokenizer"
  let preTy <- (preTokenizer.getObjVal? "type").bind Json.getStr?
  if preTy != "Sequence" then
    throw s!"unsupported pre_tokenizer.type {preTy}; expected Sequence for cl100k/o200k"
  let pretokenizers <- (preTokenizer.getObjVal? "pretokenizers").bind Json.getArr?
  if h : 0 < pretokenizers.size then
    let split := pretokenizers[0]
    let splitTy <- (split.getObjVal? "type").bind Json.getStr?
    if splitTy != "Split" then
      throw s!"unsupported first pretokenizer {splitTy}; expected Split"
    let pattern <- ((← split.getObjVal? "pattern").getObjVal? "Regex").bind Json.getStr?
    if pattern == cl100kSplitRegex then
      pure .cl100k
    else if pattern == o200kSplitRegex then
      pure .o200k
    else
      throw "unsupported Split regex; only cl100k and o200k are supported"
  else
    throw "pre_tokenizer.pretokenizers must be non-empty"

private structure LoaderState where
  tokenToInternal : Std.HashMap ByteArray TokenId
  vocab : VocabMap
  externalToInternal : Std.HashMap TokenId TokenId
  internalToExternal : Std.HashMap TokenId TokenId
  mergeList : List MergeEntry
  nextInternal : TokenId

private def initialLoaderState : LoaderState :=
  let baseBytes := List.range 256
  baseBytes.foldl
    (fun st n =>
      if h : n < 256 then
        let b : UInt8 := ⟨n, by omega⟩
        let bs := ByteArray.mk #[b]
        { st with
          tokenToInternal := st.tokenToInternal.insert bs n
          vocab := st.vocab.insert n bs }
      else st)
    { tokenToInternal := {}
      vocab := {}
      externalToInternal := {}
      internalToExternal := {}
      mergeList := []
      nextInternal := 256 }

private def seedExternalBaseIds
    (vocab : Std.HashMap String TokenId) : Except String LoaderState := do
  let mut st := initialLoaderState
  for entry in vocab.toList do
    let decoded <- decodeByteLevelToken entry.1
    if decoded.size = 1 then
      let b := decoded[0]!
      st := { st with
        externalToInternal := st.externalToInternal.insert entry.2 b.toNat
        internalToExternal := st.internalToExternal.insert b.toNat entry.2 }
  for n in List.range 256 do
    if !st.internalToExternal.contains n then
      throw s!"missing base token for byte {n}"
  pure st

private def loadAsciiTokenizerExcept (path : System.FilePath) (contents : String) :
    Except String LoadedAsciiTokenizer := do
  let root <- Json.parse contents
  let profile <- parsePreTokenizerProfile root
  let model <- root.getObjVal? "model"
  let modelTy <- (model.getObjVal? "type").bind Json.getStr?
  if modelTy != "BPE" then
    throw s!"expected model.type = BPE, got {modelTy}"
  let vocab <- parseVocab (← model.getObjVal? "vocab")
  let merges <- parseMerges (← model.getObjVal? "merges")
  let mut st <- seedExternalBaseIds vocab
  for pair in merges do
    let leftBytes <- decodeByteLevelToken pair.1
    let rightBytes <- decodeByteLevelToken pair.2
    let mergedBytes := leftBytes ++ rightBytes
    if isAsciiBytes mergedBytes then
      match st.tokenToInternal.get? leftBytes, st.tokenToInternal.get? rightBytes with
      | some leftId, some rightId =>
          match vocab.get? (pair.1 ++ pair.2) with
          | some externalId =>
              match st.tokenToInternal.get? mergedBytes with
              | some existingId =>
                  -- Token already exists via an earlier merge path;
                  -- still register this pair so the encoder can find it.
                  st := { st with
                    mergeList := ((leftId, rightId), existingId) :: st.mergeList }
              | none =>
                  let internalId := st.nextInternal
                  st := { st with
                    tokenToInternal := st.tokenToInternal.insert mergedBytes internalId
                    vocab := st.vocab.insert internalId mergedBytes
                    externalToInternal := st.externalToInternal.insert externalId internalId
                    internalToExternal := st.internalToExternal.insert internalId externalId
                    mergeList := ((leftId, rightId), internalId) :: st.mergeList
                    nextInternal := internalId + 1 }
          | none => pure ()
      | _, _ => pure ()
  if st.mergeList.isEmpty then
    throw s!"no ASCII merges found in {path}"
  pure {
    profile := profile
    merges := buildMerges st.mergeList
    vocab := st.vocab
    externalToInternal := st.externalToInternal
    internalToExternal := st.internalToExternal
  }

/-- Load the ASCII-compatible subset of a GPT-style byte-level `tokenizer.json`. -/
def loadAsciiTokenizer (path : System.FilePath := defaultTokenizerPath) :
    IO (Except String LoadedAsciiTokenizer) := do
  let contents ← IO.FS.readFile path
  pure <| loadAsciiTokenizerExcept path contents

/-- Runtime translation from an internal token id to the external tokenizer id. -/
private def encodeId (tok : LoadedAsciiTokenizer) (internalId : TokenId) :
    Except String TokenId :=
  match tok.internalToExternal.get? internalId with
  | some externalId => pure externalId
  | none => throw s!"missing external id for internal token {internalId}"

/-- Runtime translation from an external tokenizer id to the internal id. -/
private def decodeId (tok : LoadedAsciiTokenizer) (externalId : TokenId) :
    Except String TokenId :=
  match tok.externalToInternal.get? externalId with
  | some internalId => pure internalId
  | none => throw s!"token id {externalId} is not available in the ASCII subset"

private def encodeIds (tok : LoadedAsciiTokenizer) : List TokenId → Except String (List TokenId)
  | [] => pure []
  | internalId :: rest => do
      let externalId ← encodeId tok internalId
      let externalRest ← encodeIds tok rest
      pure (externalId :: externalRest)

private def decodeIds (tok : LoadedAsciiTokenizer) : List TokenId → Except String (List TokenId)
  | [] => pure []
  | externalId :: rest => do
      let internalId ← decodeId tok externalId
      let internalRest ← decodeIds tok rest
      pure (internalId :: internalRest)

/-- Encode ASCII text to external tokenizer ids. -/
def encodeExternalIds (tok : LoadedAsciiTokenizer) (text : String) :
    Except String (List TokenId) := do
  if !isAsciiString text then
    throw "only ASCII input is supported"
  let internalIds := encodeWithProfile tok.profile tok.merges tok.vocab (fun b => b) text
  encodeIds tok internalIds

/-- Decode external tokenizer ids back to text within the ASCII-supported subset. -/
def decodeExternalIds (tok : LoadedAsciiTokenizer) (ids : List TokenId) :
    Except String String := do
  let internalIds ← decodeIds tok ids
  pure <| decode tok.vocab (fun b => b) internalIds

/-- CLI-facing encode/decode wrapper over external tokenizer ids. -/
def roundtripExternal (tok : LoadedAsciiTokenizer) (text : String) :
    Except String String := do
  let ids ← encodeExternalIds tok text
  decodeExternalIds tok ids

/-- Internal ids that roundtrip cleanly through the external-id translation. -/
def InternalIdMapped (tok : LoadedAsciiTokenizer) (internalId : TokenId) : Prop :=
  ∃ externalId,
    tok.internalToExternal.get? internalId = some externalId ∧
    tok.externalToInternal.get? externalId = some internalId

/-- The external/internal id maps cover all ids that internal encoding can emit. -/
structure IdMapsSound (tok : LoadedAsciiTokenizer) : Prop where
  base_ids : ∀ i : UInt8, InternalIdMapped tok i.toNat
  merge_targets :
    ∀ p0 p1 idx, tok.merges.get? (p0, p1) = some idx → InternalIdMapped tok idx

/-- Runtime-loaded tokenizer data together with the proof obligations needed by
the abstract roundtrip theorem and the external-id bridge. -/
structure LoadedAsciiSound (tok : LoadedAsciiTokenizer) : Prop where
  encodeReady : EncodeReady tok.merges tok.vocab
  idMaps : IdMapsSound tok

private def validateBaseTokens (tok : LoadedAsciiTokenizer) : Bool :=
  (List.range 256).all fun n =>
    if h : n < 256 then
      decide (tok.vocab.getD n ByteArray.empty = ByteArray.mk #[⟨n, h⟩])
    else
      false

private def validateMergeDecomp (tok : LoadedAsciiTokenizer) : Bool :=
  tok.merges.all fun pair idx =>
    decide (
      tok.vocab.getD idx ByteArray.empty =
        tok.vocab.getD pair.1 ByteArray.empty ++
        tok.vocab.getD pair.2 ByteArray.empty)

/-- Runtime checker for the `EncodeReady` obligations. -/
def validateEncodeReady (tok : LoadedAsciiTokenizer) : Bool :=
  validateBaseTokens tok && validateMergeDecomp tok

private def validateInternalIdMap (tok : LoadedAsciiTokenizer) (internalId : TokenId) : Bool :=
  match tok.internalToExternal.get? internalId with
  | some externalId => tok.externalToInternal.get? externalId == some internalId
  | none => false

private def validateBaseIdMaps (tok : LoadedAsciiTokenizer) : Bool :=
  (List.range 256).all (validateInternalIdMap tok)

private def validateMergeTargetMaps (tok : LoadedAsciiTokenizer) : Bool :=
  tok.merges.all fun _ idx => validateInternalIdMap tok idx

/-- Runtime checker for the external/internal id translation used by the CLI. -/
def validateIdMaps (tok : LoadedAsciiTokenizer) : Bool :=
  validateBaseIdMaps tok && validateMergeTargetMaps tok

/-- Combined validator for the runtime-loaded artifact. -/
def validateLoadedAsciiTokenizer (tok : LoadedAsciiTokenizer) : Bool :=
  validateEncodeReady tok && validateIdMaps tok

private theorem internalIdMapped_of_validateInternalIdMap
    (tok : LoadedAsciiTokenizer)
    (internalId : TokenId)
    (hvalid : validateInternalIdMap tok internalId = true) :
    InternalIdMapped tok internalId := by
  cases hget : tok.internalToExternal[internalId]? with
  | none =>
      simp [validateInternalIdMap, hget] at hvalid
  | some externalId =>
      have hback : tok.externalToInternal.get? externalId = some internalId := by
        simpa [validateInternalIdMap, hget, beq_iff_eq] using hvalid
      refine ⟨externalId, by simpa using hget, ?_⟩
      exact hback

private theorem baseTokens_of_validateBaseTokens
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateBaseTokens tok = true) :
    ∀ i : UInt8, tok.vocab.getD i.toNat ByteArray.empty = ByteArray.mk #[i] := by
  intro i
  have hi_mem : i.toNat ∈ List.range 256 := by simpa using i.toNat_lt
  have hi_valid := List.all_eq_true.mp hvalid i.toNat hi_mem
  have hi_eq : (⟨i.toNat, i.toNat_lt⟩ : UInt8) = i := by
    cases i
    rfl
  have hdec : decide (tok.vocab.getD i.toNat ByteArray.empty = ByteArray.mk #[i]) = true := by
    simpa [validateBaseTokens, i.toNat_lt, hi_eq] using hi_valid
  simpa [decide_eq_true_eq] using hdec

private theorem mergeDecomp_of_validateMergeDecomp
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateMergeDecomp tok = true)
    {p0 p1 idx : TokenId}
    (hget : tok.merges.get? (p0, p1) = some idx) :
    tok.vocab.getD idx ByteArray.empty =
      tok.vocab.getD p0 ByteArray.empty ++
      tok.vocab.getD p1 ByteArray.empty := by
  have hget' : tok.merges[(p0, p1)]? = some idx := by simpa using hget
  have hmem : (p0, p1) ∈ tok.merges :=
    (Std.HashMap.getElem?_eq_some_iff.mp hget').1
  have hall := (Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp hvalid) (p0, p1) hmem
  have hsome := Std.HashMap.getElem?_eq_some_getElem hmem
  rw [hget'] at hsome
  injection hsome with hEq
  have hdec :
      decide (
        tok.vocab.getD tok.merges[(p0, p1)] ByteArray.empty =
          (tok.vocab.getD p0 ByteArray.empty ++ tok.vocab.getD p1 ByteArray.empty)) = true := by
    simpa [hEq] using hall
  have hstored :
      tok.vocab.getD tok.merges[(p0, p1)] ByteArray.empty =
        tok.vocab.getD p0 ByteArray.empty ++ tok.vocab.getD p1 ByteArray.empty :=
    by simpa [decide_eq_true_eq] using hdec
  simpa [hEq] using hstored

/-- Reflection theorem: the boolean validator is sufficient for `EncodeReady`. -/
theorem encodeReady_of_validateEncodeReady
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateEncodeReady tok = true) :
    EncodeReady tok.merges tok.vocab := by
  have hparts : validateBaseTokens tok = true ∧ validateMergeDecomp tok = true := by
    simpa [validateEncodeReady, Bool.and_eq_true] using hvalid
  refine {
    base_tokens := baseTokens_of_validateBaseTokens tok hparts.1
    merge_decomp := ?_
  }
  intro p0 p1 idx hgetD hcontains
  have hget : tok.merges[(p0, p1)]? = some idx := by
    rw [Std.HashMap.getElem?_eq_some_getD_of_contains
      (m := tok.merges) (a := (p0, p1)) (fallback := 0) hcontains]
    simpa using congrArg some hgetD
  exact mergeDecomp_of_validateMergeDecomp tok hparts.2 (by simpa using hget)

private theorem mergeTargetMapped_of_validateMergeTargetMaps
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateMergeTargetMaps tok = true)
    {p0 p1 idx : TokenId}
    (hget : tok.merges.get? (p0, p1) = some idx) :
    InternalIdMapped tok idx := by
  have hget' : tok.merges[(p0, p1)]? = some idx := by simpa using hget
  have hmem : (p0, p1) ∈ tok.merges :=
    (Std.HashMap.getElem?_eq_some_iff.mp hget').1
  have hall := (Std.HashMap.all_eq_true_iff_forall_mem_getElem.mp hvalid) (p0, p1) hmem
  have hsome := Std.HashMap.getElem?_eq_some_getElem hmem
  rw [hget'] at hsome
  injection hsome with hEq
  exact internalIdMapped_of_validateInternalIdMap tok idx (by simpa [hEq] using hall)

/-- Reflection theorem: the id-map validator is sufficient for the CLI bridge. -/
theorem idMapsSound_of_validateIdMaps
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateIdMaps tok = true) :
    IdMapsSound tok := by
  have hparts : validateBaseIdMaps tok = true ∧ validateMergeTargetMaps tok = true := by
    simpa [validateIdMaps, Bool.and_eq_true] using hvalid
  refine {
    base_ids := ?_
    merge_targets := ?_
  }
  · intro i
    have hi_mem : i.toNat ∈ List.range 256 := by simpa using i.toNat_lt
    have hi_valid := List.all_eq_true.mp hparts.1 i.toNat hi_mem
    exact internalIdMapped_of_validateInternalIdMap tok i.toNat hi_valid
  · intro p0 p1 idx hget
    exact mergeTargetMapped_of_validateMergeTargetMaps tok hparts.2 hget

/-- Reflection theorem for the combined runtime validator. -/
theorem loadedAsciiSound_of_validate
    (tok : LoadedAsciiTokenizer)
    (hvalid : validateLoadedAsciiTokenizer tok = true) :
    LoadedAsciiSound tok := by
  have hparts : validateEncodeReady tok = true ∧ validateIdMaps tok = true := by
    simpa [validateLoadedAsciiTokenizer, Bool.and_eq_true] using hvalid
  exact {
    encodeReady := encodeReady_of_validateEncodeReady tok hparts.1
    idMaps := idMapsSound_of_validateIdMaps tok hparts.2
  }

private theorem isAsciiString_eq_true_of_hascii
    (s : String)
    (hascii : ∀ c ∈ s.toList, c.val < 128) :
    isAsciiString s = true := by
  unfold isAsciiString
  apply List.all_eq_true.mpr
  intro c hc
  simpa using hascii c hc

private theorem encodeDecodeIds_roundtrip
    (tok : LoadedAsciiTokenizer) :
    ∀ (ids : List TokenId),
      (∀ id ∈ ids, InternalIdMapped tok id) →
      (do
        let externalIds ← encodeIds tok ids
        decodeIds tok externalIds) = .ok ids := by
  intro ids
  induction ids with
  | nil =>
      intro hids
      rfl
  | cons id ids ih =>
      intro hids
      rcases hids id (by simp) with ⟨externalId, henc, hdec⟩
      have htail : ∀ id' ∈ ids, InternalIdMapped tok id' := by
        intro id' hid'
        exact hids id' (by simp [hid'])
      have hencodeId : encodeId tok id = .ok externalId := by
        unfold encodeId
        rw [henc]
        rfl
      have hdecodeId : decodeId tok externalId = .ok id := by
        unfold decodeId
        rw [hdec]
        rfl
      have htailRound := ih htail
      cases hrest : encodeIds tok ids with
      | error err =>
          rw [hrest] at htailRound
          cases htailRound
      | ok externalRest =>
          rw [hrest] at htailRound
          have hdecodeRest : decodeIds tok externalRest = .ok ids := by
            simpa using htailRound
          have henc : encodeIds tok (id :: ids) = .ok (externalId :: externalRest) := by
            change (encodeId tok id >>= fun e =>
                    encodeIds tok ids >>= fun r => pure (e :: r))
                  = .ok (externalId :: externalRest)
            rw [hencodeId, hrest]; rfl
          have hdec : decodeIds tok (externalId :: externalRest) = .ok (id :: ids) := by
            change (decodeId tok externalId >>= fun i =>
                    decodeIds tok externalRest >>= fun r => pure (i :: r))
                  = .ok (id :: ids)
            rw [hdecodeId, hdecodeRest]; rfl
          change encodeIds tok (id :: ids) >>= decodeIds tok = .ok (id :: ids)
          rw [henc]
          exact hdec

/-- End-to-end theorem for the runtime-loaded artifact and user-facing external
ids. -/
theorem roundtripExternal_ok_of_sound
    (tok : LoadedAsciiTokenizer)
    (hsound : LoadedAsciiSound tok)
    (s : String)
    (hascii : ∀ c ∈ s.toList, c.val < 128) :
    roundtripExternal tok s = .ok s := by
  unfold roundtripExternal encodeExternalIds decodeExternalIds
  simp [isAsciiString_eq_true_of_hascii s hascii]
  let internalIds := encodeWithProfile tok.profile tok.merges tok.vocab (fun b => b) s
  have hmapped : ∀ id ∈ internalIds, InternalIdMapped tok id := by
    intro id hid
    have hbase : ∀ b : UInt8, InternalIdMapped tok b.toNat := hsound.idMaps.base_ids
    have hmerge : ∀ p0 p1 idx, tok.merges.get? (p0, p1) = some idx → InternalIdMapped tok idx :=
      hsound.idMaps.merge_targets
    exact encodeWithProfile_preserves tok.profile tok.merges tok.vocab (fun b => b) s
      (P := InternalIdMapped tok) hbase hmerge id hid
  have htranslate : (do
      let externalIds ← encodeIds tok internalIds
      decodeIds tok externalIds) = .ok internalIds :=
    encodeDecodeIds_roundtrip tok internalIds hmapped
  have hdecoded :
      (do
        let ids ← encodeIds tok internalIds
        (decode tok.vocab (fun b => b)) <$> decodeIds tok ids) =
      .ok (decode tok.vocab (fun b => b) internalIds) := by
    cases hencs : encodeIds tok internalIds with
    | error err =>
        rw [hencs] at htranslate
        cases htranslate
    | ok externalIds =>
        rw [hencs] at htranslate
        have hdecodeIds : decodeIds tok externalIds = .ok internalIds := by
          simpa using htranslate
        change (decode tok.vocab (fun b => b)) <$> decodeIds tok externalIds =
          .ok (decode tok.vocab (fun b => b) internalIds)
        rw [hdecodeIds]
        rfl
  have hround : decode tok.vocab (fun b => b) internalIds = s := by
    simpa [internalIds] using ascii_bpe_roundtrip_of_encodeReady_withProfile
      tok.profile tok.merges tok.vocab (fun b => b) (fun b => b)
      hsound.encodeReady (by intro b; rfl) s hascii
  simpa [hround] using hdecoded

/-- Load a tokenizer and reject it unless the runtime validator can certify the
proof obligations needed by the external-id roundtrip theorem. -/
def loadVerifiedAsciiTokenizer (path : System.FilePath := defaultTokenizerPath) :
    IO (Except String { tok : LoadedAsciiTokenizer // LoadedAsciiSound tok }) := do
  let result ← loadAsciiTokenizer path
  pure <| match result with
    | .error err => .error err
    | .ok tok =>
        if hvalid : validateLoadedAsciiTokenizer tok = true then
          .ok ⟨tok, loadedAsciiSound_of_validate tok hvalid⟩
        else
          .error "loaded tokenizer failed validation"

end BPE
