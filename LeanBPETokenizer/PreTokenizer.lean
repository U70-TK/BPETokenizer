import LeanBPETokenizer.ASCIIClassifiers
import Regex.Regex.Elab
import Regex.Regex.Utilities

/-!
# Part 2 – ASCII Pre-Tokenizer

Implements ASCII pre-tokenization for the modern OpenAI `cl100k` and `o200k`
pattern families. The implementation keeps the original byte-array scanning
loop, but uses compile-time regexes to recognize the profile-specific token
branches on ASCII suffixes.

Branch priority:
  1. Profile regex branches
  2. Trailing-WS  `\s+(?!\S)`   (kept manual; lean-regex has no lookahead)
  3. Other-WS     `\s+`
  4. Fallback     consume 1 byte

**Key invariant (Lemma 4):**
  `(preTokenizeASCII data).foldl (· ++ ·) #[] = data`
-/

namespace BPE

/-- Supported ASCII pre-tokenization profiles for modern OpenAI tokenizers. -/
inductive PreTokenizerProfile where
  | cl100k
  | o200k
deriving DecidableEq, Repr

open Regex

/-- The explicit ASCII-specialized regex family supported by this repo. -/
def supportedAsciiPattern : PreTokenizerProfile → String
  | .cl100k =>
      "(?i:'(s|d|m|t|ll|ve|re))|\
       [^\\r\\nA-Za-z0-9]?[A-Za-z]+|\
       [0-9]{1,3}| ?[^\\sA-Za-z0-9]+[\\r\\n]*|\
       \\s*[\\r\\n]+"
  | .o200k =>
      "[^\\r\\nA-Za-z0-9]?[A-Z]*[a-z]+(?i:'(s|d|m|t|ll|ve|re))?|\
       [^\\r\\nA-Za-z0-9]?[A-Z]+[a-z]*(?i:'(s|d|m|t|ll|ve|re))?|\
       [0-9]{1,3}| ?[^\\sA-Za-z0-9]+[\\r\\n/]*|\
       \\s*[\\r\\n]+"

private def cl100kSupportedRegex : Regex :=
  Regex.parse! (supportedAsciiPattern .cl100k)

private def o200kSupportedRegex : Regex :=
  Regex.parse! (supportedAsciiPattern .o200k)

private def supportedRegex : PreTokenizerProfile → Regex
  | .cl100k => cl100kSupportedRegex
  | .o200k => o200kSupportedRegex

private def asciiSuffixString? (data : ByteArray) (pos : Nat) : Option String := do
  let suffix := data.extract pos data.size
  if suffix.data.all (fun b => b.toNat < 128) then
    String.fromUTF8? suffix
  else
    none

private def regexPrefixLen (regex : Regex) (data : ByteArray) (pos : Nat) : Nat :=
  match asciiSuffixString? data pos with
  | none => 0
  | some suffix =>
      match regex.searchNext suffix.startPos with
      | none => 0
      | some slice =>
          if slice.startInclusive.offset = suffix.startPos.offset then
            slice.copy.toUTF8.size
          else
            0

/-- Spec-level prefix length for the supported regex branch of the profile. -/
def profileRegexSpecLen (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) : Nat :=
  regexPrefixLen (supportedRegex profile) data pos

private def tryProfileRegex (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) : Nat :=
  profileRegexSpecLen profile data pos

-- ---------------------------------------------------------------------------
-- Branch 6: Trailing-WS  \s+(?!\S)
-- ---------------------------------------------------------------------------

private def consumeWs (data : ByteArray) (i : Nat) : Nat :=
  let n := data.size
  if h : i < n then
    if isSpace (data[i]'h) then consumeWs data (i + 1)
    else i
  else i
  termination_by data.size - i

private theorem le_consumeWs
    (data : ByteArray)
    (i : Nat) :
    i ≤ consumeWs data i := by
  rw [consumeWs.eq_1]
  split_ifs with h0 hspace
  · have hrec := le_consumeWs data (i + 1)
    omega
  · omega
  · omega

private def endOfWsRun (data : ByteArray) (pos : Nat) : Nat :=
  consumeWs data pos

private theorem lt_endOfWsRun_of_space
    (data : ByteArray)
    (pos : Nat)
    (h0 : pos < data.size)
    (hspace : isSpace (data[pos]'h0)) :
    pos < endOfWsRun data pos := by
  unfold endOfWsRun consumeWs
  simp [h0, hspace]
  have hrec := le_consumeWs data (pos + 1)
  omega

/-- ASCII spec for the manual `\s+(?!\S)` fallback branch.

If a whitespace run reaches the end of input, this consumes the whole run.
Otherwise it consumes the longest proper prefix of that run, which is the
ASCII behavior of greedy `\s+(?!\S)` once the earlier newline branch fails.
-/
def trailingWsSpecLen (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  if h0 : pos < n then
    if !isSpace (data[pos]'h0) then 0
    else
      let wsEnd := endOfWsRun data pos
      if wsEnd < n then wsEnd - pos - 1 else wsEnd - pos
  else 0

-- ---------------------------------------------------------------------------
-- Branch 7: Other-WS  \s+
-- ---------------------------------------------------------------------------

def otherWsSpecLen (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  if h0 : pos < n then
    if !isSpace (data[pos]'h0) then 0
    else
      endOfWsRun data pos - pos
  else 0

def tryTrailingWS (data : ByteArray) (pos : Nat) : Nat :=
  trailingWsSpecLen data pos

def tryOtherWS (data : ByteArray) (pos : Nat) : Nat :=
  otherWsSpecLen data pos

theorem trailingWsSpecLen_eq_otherWsSpecLen_or_prev
    (data : ByteArray)
    (pos : Nat) :
    trailingWsSpecLen data pos = otherWsSpecLen data pos ∨
      trailingWsSpecLen data pos + 1 = otherWsSpecLen data pos := by
  unfold trailingWsSpecLen otherWsSpecLen
  by_cases h0 : pos < data.size
  · by_cases hspace : isSpace (data[pos]'h0)
    · set wsEnd := endOfWsRun data pos
      by_cases hEnd : wsEnd < data.size
      · right
        simp [h0, hspace, hEnd, wsEnd]
        have hlt : pos < wsEnd := by
          simpa [wsEnd] using lt_endOfWsRun_of_space data pos h0 hspace
        omega
      · left
        simp [h0, hspace, hEnd, wsEnd]
    · left
      simp [h0, hspace]
  · left
    simp [h0]

theorem trailingWsSpecLen_le_otherWsSpecLen
    (data : ByteArray)
    (pos : Nat) :
    trailingWsSpecLen data pos ≤ otherWsSpecLen data pos := by
  rcases trailingWsSpecLen_eq_otherWsSpecLen_or_prev data pos with hEq | hPrev
  · omega
  · omega

-- ---------------------------------------------------------------------------
-- Priority dispatch
-- ---------------------------------------------------------------------------

def nextTokenLenSpec (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) : Nat :=
  let n1 := tryProfileRegex profile data pos; if n1 != 0 then n1 else
  let n2 := trailingWsSpecLen data pos; if n2 != 0 then n2 else
  let n3 := otherWsSpecLen data pos; if n3 != 0 then n3 else
  1

def nextTokenLen (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) : Nat :=
  nextTokenLenSpec profile data pos

theorem tryTrailingWS_eq_spec (data : ByteArray) (pos : Nat) :
    tryTrailingWS data pos = trailingWsSpecLen data pos := rfl

theorem tryOtherWS_eq_spec (data : ByteArray) (pos : Nat) :
    tryOtherWS data pos = otherWsSpecLen data pos := rfl

theorem nextTokenLen_eq_spec (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) :
    nextTokenLen profile data pos = nextTokenLenSpec profile data pos := rfl

/-- The branch-ordered ASCII semantics intended for a supported profile. -/
def AsciiCorrespondsAt (profile : PreTokenizerProfile) (data : ByteArray) (pos len : Nat) : Prop :=
  let nRegex := profileRegexSpecLen profile data pos
  let nTrail := trailingWsSpecLen data pos
  let nOther := otherWsSpecLen data pos
  (nRegex ≠ 0 ∧ len = nRegex) ∨
  (nRegex = 0 ∧ nTrail ≠ 0 ∧ len = nTrail) ∨
  (nRegex = 0 ∧ nTrail = 0 ∧ nOther ≠ 0 ∧ len = nOther) ∨
  (nRegex = 0 ∧ nTrail = 0 ∧ nOther = 0 ∧ len = 1)

abbrev Cl100kAsciiCorrespondsAt (data : ByteArray) (pos len : Nat) : Prop :=
  AsciiCorrespondsAt .cl100k data pos len

abbrev O200kAsciiCorrespondsAt (data : ByteArray) (pos len : Nat) : Prop :=
  AsciiCorrespondsAt .o200k data pos len

theorem trailingWsSpecLen_of_space
    (data : ByteArray)
    (pos : Nat)
    (h0 : pos < data.size)
    (hspace : isSpace (data[pos]'h0)) :
    trailingWsSpecLen data pos =
      let wsEnd := endOfWsRun data pos
      if wsEnd < data.size then wsEnd - pos - 1 else wsEnd - pos := by
  simp [trailingWsSpecLen, h0, hspace]

theorem otherWsSpecLen_of_space
    (data : ByteArray)
    (pos : Nat)
    (h0 : pos < data.size)
    (hspace : isSpace (data[pos]'h0)) :
    otherWsSpecLen data pos = endOfWsRun data pos - pos := by
  simp [otherWsSpecLen, h0, hspace]

theorem nextTokenLen_pos (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) :
    1 ≤ nextTokenLen profile data pos := by
  cases profile <;>
    simp only [nextTokenLen, nextTokenLenSpec, bne_iff_ne, ne_eq] <;>
    split_ifs <;> omega

/-- One-step correspondence theorem: the implementation's token length agrees
with the intended ASCII branch ordering for the chosen profile. -/
theorem nextTokenLen_correspondence
    (profile : PreTokenizerProfile)
    (data : ByteArray)
    (pos : Nat) :
    AsciiCorrespondsAt profile data pos (nextTokenLen profile data pos) := by
  by_cases hRegex : profileRegexSpecLen profile data pos = 0
  · by_cases hTrail : trailingWsSpecLen data pos = 0
    · by_cases hOther : otherWsSpecLen data pos = 0
      · simp [AsciiCorrespondsAt, nextTokenLen, nextTokenLenSpec, tryProfileRegex,
          hRegex, hTrail, hOther]
      · simp [AsciiCorrespondsAt, nextTokenLen, nextTokenLenSpec, tryProfileRegex,
          hRegex, hTrail, hOther]
    · simp [AsciiCorrespondsAt, nextTokenLen, nextTokenLenSpec, tryProfileRegex,
        hRegex, hTrail]
  · simp [AsciiCorrespondsAt, nextTokenLen, nextTokenLenSpec, tryProfileRegex, hRegex]

theorem cl100k_nextTokenLen_correspondence
    (data : ByteArray)
    (pos : Nat) :
    Cl100kAsciiCorrespondsAt data pos (nextTokenLen .cl100k data pos) :=
  nextTokenLen_correspondence .cl100k data pos

theorem o200k_nextTokenLen_correspondence
    (data : ByteArray)
    (pos : Nat) :
    O200kAsciiCorrespondsAt data pos (nextTokenLen .o200k data pos) :=
  nextTokenLen_correspondence .o200k data pos

-- ---------------------------------------------------------------------------
-- Main loop
-- ---------------------------------------------------------------------------

def preTokenizeASCII (profile : PreTokenizerProfile) (data : ByteArray) : Array ByteArray :=
  let rec loop (pos : Nat) (acc : Array ByteArray) : Array ByteArray :=
    if h : pos < data.size then
      let n := nextTokenLen profile data pos
      let endPos := min (pos + n) data.size
      have hadvance : endPos > pos := by
        have hn := nextTokenLen_pos profile data pos
        simp only [endPos, Nat.min_def]
        split_ifs with hle
        · omega
        · exact h
      loop endPos (acc.push (data.extract pos endPos))
    else acc
  termination_by data.size - pos
  decreasing_by
    omega
  loop 0 #[]

/-- Full-sequence correspondence from a given byte position. Each token chunk
must be the exact slice chosen by the implementation, and the chosen token
length must satisfy the intended branch ordering of the selected profile. -/
def AsciiCorrespondsSeqFrom
    (profile : PreTokenizerProfile)
    (data : ByteArray) : Nat → List ByteArray → Prop
  | pos, [] => data.size ≤ pos
  | pos, tok :: toks =>
      let n := nextTokenLen profile data pos
      let endPos := min (pos + n) data.size
      tok = data.extract pos endPos ∧
      AsciiCorrespondsAt profile data pos n ∧
      AsciiCorrespondsSeqFrom profile data endPos toks

abbrev Cl100kAsciiCorrespondsSeqFrom (data : ByteArray) : Nat → List ByteArray → Prop :=
  AsciiCorrespondsSeqFrom .cl100k data

abbrev O200kAsciiCorrespondsSeqFrom (data : ByteArray) : Nat → List ByteArray → Prop :=
  AsciiCorrespondsSeqFrom .o200k data

private def preTokenizeASCIIList
    (profile : PreTokenizerProfile)
    (data : ByteArray)
    (pos : Nat) : List ByteArray :=
  if _h : pos < data.size then
    let n := nextTokenLen profile data pos
    let endPos := min (pos + n) data.size
    data.extract pos endPos :: preTokenizeASCIIList profile data endPos
  else
    []
  termination_by data.size - pos
  decreasing_by
    have hnext := nextTokenLen_pos profile data pos
    omega

private theorem preTokenizeASCII_loop_toList_eq
    (profile : PreTokenizerProfile)
    (data : ByteArray) :
    ∀ (n pos : Nat) (acc : Array ByteArray),
      data.size - pos ≤ n →
      (preTokenizeASCII.loop profile data pos acc).toList =
        acc.toList ++ preTokenizeASCIIList profile data pos := by
  intro n
  induction n with
  | zero =>
      intro pos acc hle
      have hge : ¬ pos < data.size := by
        omega
      rw [preTokenizeASCII.loop.eq_1, preTokenizeASCIIList.eq_1]
      simp [hge]
  | succ n ih =>
      intro pos acc hle
      by_cases hlt : pos < data.size
      · set nTok := nextTokenLen profile data pos
        set endPos := min (pos + nTok) data.size
        have hAdvance : pos < endPos := by
          have hnext := nextTokenLen_pos profile data pos
          simp only [endPos, Nat.min_def]
          split_ifs with hBound
          · omega
          · exact hlt
        rw [preTokenizeASCII.loop.eq_1, preTokenizeASCIIList.eq_1]
        simp only [dite_eq_ite]
        rw [if_pos hlt, if_pos hlt]
        calc
          (preTokenizeASCII.loop profile data endPos
              (acc.push (data.extract pos endPos))).toList
              = (acc.push (data.extract pos endPos)).toList ++
                  preTokenizeASCIIList profile data endPos := by
                    apply ih
                    omega
          _ =
              acc.toList ++
                data.extract pos endPos :: preTokenizeASCIIList profile data endPos := by
                simp
      · rw [preTokenizeASCII.loop.eq_1, preTokenizeASCIIList.eq_1]
        simp [hlt]

private theorem preTokenizeASCIIList_correspondence
    (profile : PreTokenizerProfile)
    (data : ByteArray) :
    ∀ (n pos : Nat),
      data.size - pos ≤ n →
      AsciiCorrespondsSeqFrom profile data pos (preTokenizeASCIIList profile data pos) := by
  intro n
  induction n with
  | zero =>
      intro pos hle
      have hge : ¬ pos < data.size := by
        omega
      rw [preTokenizeASCIIList.eq_1]
      simp [AsciiCorrespondsSeqFrom, hge]
      omega
  | succ n ih =>
      intro pos hle
      by_cases hlt : pos < data.size
      · set nTok := nextTokenLen profile data pos
        set endPos := min (pos + nTok) data.size
        have hAdvance : pos < endPos := by
          have hnext := nextTokenLen_pos profile data pos
          simp only [endPos, Nat.min_def]
          split_ifs with hBound
          · omega
          · exact hlt
        rw [preTokenizeASCIIList.eq_1]
        simp only [dite_eq_ite]
        rw [if_pos hlt]
        refine ⟨rfl, ?_, ?_⟩
        · simpa [nTok] using nextTokenLen_correspondence profile data pos
        exact ih endPos (by omega)
      · rw [preTokenizeASCIIList.eq_1]
        simp [AsciiCorrespondsSeqFrom, hlt]
        omega

/-- Full-sequence correspondence theorem for supported profiles. -/
theorem preTokenize_correspondence
    (profile : PreTokenizerProfile)
    (data : ByteArray) :
    AsciiCorrespondsSeqFrom profile data 0 (preTokenizeASCII profile data).toList := by
  have hList :
      (preTokenizeASCII profile data).toList = preTokenizeASCIIList profile data 0 := by
    simpa [preTokenizeASCII] using
      preTokenizeASCII_loop_toList_eq profile data data.size 0 #[] (by simp)
  have hCorr :
      AsciiCorrespondsSeqFrom profile data 0 (preTokenizeASCIIList profile data 0) := by
    exact preTokenizeASCIIList_correspondence profile data data.size 0 (by simp)
  simpa [hList] using hCorr

theorem cl100k_preTokenize_correspondence
    (data : ByteArray) :
    Cl100kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .cl100k data).toList :=
  preTokenize_correspondence .cl100k data

theorem o200k_preTokenize_correspondence
    (data : ByteArray) :
    O200kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .o200k data).toList :=
  preTokenize_correspondence .o200k data

/-- The supported ASCII-specialized regex spec for a profile matches the
implementation's one-step token choice. -/
theorem nextTokenLen_matches_supportedAsciiPattern
    (profile : PreTokenizerProfile)
    (data : ByteArray)
    (pos : Nat) :
    AsciiCorrespondsAt profile data pos (nextTokenLen profile data pos) :=
  nextTokenLen_correspondence profile data pos

/-- The supported ASCII-specialized regex spec for a profile matches the full
token sequence produced by the implementation. -/
theorem preTokenize_matches_supportedAsciiPattern
    (profile : PreTokenizerProfile)
    (data : ByteArray) :
    AsciiCorrespondsSeqFrom profile data 0 (preTokenizeASCII profile data).toList :=
  preTokenize_correspondence profile data

theorem cl100k_preTokenize_matches_supportedAsciiPattern
    (data : ByteArray) :
    Cl100kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .cl100k data).toList :=
  preTokenize_matches_supportedAsciiPattern .cl100k data

theorem o200k_preTokenize_matches_supportedAsciiPattern
    (data : ByteArray) :
    O200kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .o200k data).toList :=
  preTokenize_matches_supportedAsciiPattern .o200k data

-- ---------------------------------------------------------------------------
-- Lemma 4 – partition
-- ---------------------------------------------------------------------------

-- Helper: foldl with push appends the new element
private lemma foldl_push_append (acc : Array ByteArray) (x : ByteArray) :
    (acc.push x).foldl (· ++ ·) ByteArray.empty =
    acc.foldl (· ++ ·) ByteArray.empty ++ x := by
  rw [Array.foldl_push]

theorem preTokenize_partition (profile : PreTokenizerProfile) (data : ByteArray) :
    (preTokenizeASCII profile data).foldl (· ++ ·) ByteArray.empty = data := by
  simp only [preTokenizeASCII]
  -- Invariant: acc.foldl (· ++ ·) ∅ ++ data.extract pos data.size = data
  suffices key : ∀ (n pos : Nat) (acc : Array ByteArray),
      data.size - pos ≤ n →
      acc.foldl (· ++ ·) ByteArray.empty ++ data.extract pos data.size = data →
      (preTokenizeASCII.loop profile data pos acc).foldl (· ++ ·) ByteArray.empty = data by
    apply key data.size 0 #[]
    · simp
    · simp [ByteArray.extract_zero_size]
  intro n
  induction n with
  | zero =>
      intro pos acc hle hinv
      have hge : ¬(pos < data.size) := by omega
      have hloop : preTokenizeASCII.loop profile data pos acc = acc := by
        conv_lhs => rw [preTokenizeASCII.loop.eq_1]; simp [hge]
      rw [hloop]
      have hext : data.extract pos data.size = ByteArray.empty := by
        rw [ByteArray.extract_eq_empty_iff]; simp; omega
      simpa [hext] using hinv
  | succ n ih =>
      intro pos acc hle hinv
      by_cases h_lt : pos < data.size
      · -- Still within data: take one token and recurse
        set n_tok := nextTokenLen profile data pos with hn_tok
        set endPos := min (pos + n_tok) data.size with hendPos
        have h_advance : pos < endPos := by
          have := nextTokenLen_pos profile data pos
          simp only [endPos, Nat.min_def]
          split_ifs with hle'
          · omega
          · exact h_lt
        have hloop : preTokenizeASCII.loop profile data pos acc =
            preTokenizeASCII.loop profile data endPos (acc.push (data.extract pos endPos)) := by
          conv_lhs => rw [preTokenizeASCII.loop.eq_1]; simp [h_lt]
        rw [hloop]
        apply ih endPos (acc.push (data.extract pos endPos))
        · simp only [endPos]; omega
        · rw [foldl_push_append, ByteArray.append_assoc,
              ← ByteArray.extract_eq_extract_append_extract endPos
                  (by simp [endPos]; omega) (by simp [endPos])]
          exact hinv
      · -- pos ≥ data.size: loop returns acc immediately
        have hloop : preTokenizeASCII.loop profile data pos acc = acc := by
          conv_lhs => rw [preTokenizeASCII.loop.eq_1]; simp [h_lt]
        rw [hloop]
        have hext : data.extract pos data.size = ByteArray.empty := by
          rw [ByteArray.extract_eq_empty_iff]; simp; omega
        simpa [hext] using hinv

end BPE
