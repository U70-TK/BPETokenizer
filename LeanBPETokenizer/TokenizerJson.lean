import LeanBPETokenizer.EncDec
import Lean.Data.Json.Parser

namespace BPE

open Lean

/-- Default tokenizer path used by the CLI. -/
def defaultTokenizerPath : System.FilePath := "tokenizer.json"

/-- Runtime tokenizer built from the ASCII-compatible subset of a GPT byte-level BPE JSON. -/
structure LoadedAsciiTokenizer where
  merges : MergeMap
  vocab : VocabMap
  externalToInternal : Std.HashMap TokenId TokenId
  internalToExternal : Std.HashMap TokenId TokenId

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
    let parts <- entry.getArr?
    if h : parts.size = 2 then
      let left <- (parts[0]).getStr?
      let right <- (parts[1]).getStr?
      out := out.push (left, right)
    else
      throw s!"merge entry must have length 2, got {parts.size}"
  pure out

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
      if b.toNat < 128 then
        st := { st with
          externalToInternal := st.externalToInternal.insert entry.2 b.toNat
          internalToExternal := st.internalToExternal.insert b.toNat entry.2 }
  for n in List.range 128 do
    if !st.internalToExternal.contains n then
      throw s!"missing ASCII base token for byte {n}"
  pure st

private def loadAsciiTokenizerExcept (path : System.FilePath) (contents : String) :
    Except String LoadedAsciiTokenizer := do
  let root <- Json.parse contents
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

/-- Encode ASCII text to external tokenizer ids. -/
def encodeExternalIds (tok : LoadedAsciiTokenizer) (text : String) :
    Except String (List TokenId) := do
  if !isAsciiString text then
    throw "only ASCII input is supported"
  let internalIds := encode tok.merges tok.vocab (fun b => b) text
  internalIds.mapM fun internalId =>
    match tok.internalToExternal.get? internalId with
    | some externalId => pure externalId
    | none => throw s!"missing external id for internal token {internalId}"

/-- Decode external tokenizer ids back to text within the ASCII-supported subset. -/
def decodeExternalIds (tok : LoadedAsciiTokenizer) (ids : List TokenId) :
    Except String String := do
  let internalIds ← ids.mapM fun externalId =>
    match tok.externalToInternal.get? externalId with
    | some internalId => pure internalId
    | none => throw s!"token id {externalId} is not available in the ASCII subset"
  pure <| decode tok.vocab (fun b => b) internalIds

end BPE
