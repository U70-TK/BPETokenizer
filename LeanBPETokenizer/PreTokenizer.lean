import LeanBPETokenizer.ASCIIClassifiers

/-!
# Part 2 – ASCII Pre-Tokenizer (Finite-State Machine)

Implements the GPT-4 `cl100k_base` split pattern restricted to ASCII input.
Each branch function has signature `ByteArray → Nat → Nat`, returning the
number of bytes consumed at position `pos`, or `0` on no-match.

Branch priority:
  1. Contraction  `'(?i:[sdmt]|ll|ve|re)`
  2. Word         `[^\r\n\p{L}\p{N}]?\p{L}+`
  3. Digits       `\p{N}{1,3}`
  4. Punctuation  `' '?[^\s\p{L}\p{N}]++[\r\n]*`
  5. Newline-WS   `\s*[\r\n]`
  6. Trailing-WS  `\s+(?!\S)`
  7. Other-WS     `\s+`
  8. Fallback     consume 1 byte

**Key invariant (Lemma 4):**
  `(preTokenizeASCII data).foldl (· ++ ·) #[] = data`
-/

namespace BPE

/-- Supported ASCII pre-tokenization profiles for modern OpenAI tokenizers. -/
inductive PreTokenizerProfile where
  | cl100k
  | o200k
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- Branch 1: Contraction  '(?i:[sdmt]|ll|ve|re)
-- ---------------------------------------------------------------------------

def tryContraction (data : ByteArray) (pos : Nat) : Nat :=
  if h0 : pos < data.size then
    if data[pos]'h0 != 39 then 0
    else if h1 : pos + 1 < data.size then
      let c := toLower (data[pos + 1]'h1)
      if c == 115 || c == 100 || c == 109 || c == 116 then 2
      else if h2 : pos + 2 < data.size then
        let c2 := toLower (data[pos + 2]'h2)
        if c == 108 && c2 == 108 then 3
        else if c == 118 && c2 == 101 then 3
        else if c == 114 && c2 == 101 then 3
        else 0
      else 0
    else 0
  else 0

private def contractionSuffixLenAt (data : ByteArray) (pos : Nat) : Nat :=
  tryContraction data pos

-- ---------------------------------------------------------------------------
-- Branch 2: Word  [^\r\n\p{L}\p{N}]?\p{L}+
-- ---------------------------------------------------------------------------

def tryWord (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  -- optional leading byte: not newline, not letter, not digit
  let i₁ : Nat :=
    if h : pos < n then
      let b := data[pos]'h
      if !isNewline b && !isLetter b && !isDigit b then pos + 1 else pos
    else pos
  if hi : i₁ < n then
    if !isLetter (data[i₁]'hi) then 0
    else
      let rec consumeLetters (i : Nat) : Nat :=
        if h : i < n then
          if isLetter (data[i]'h) then consumeLetters (i + 1)
          else i
        else i
      termination_by data.size - i
      (consumeLetters i₁) - pos
  else 0

private def tryWordLowerSuffix (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  let i₁ : Nat :=
    if h : pos < n then
      let b := data[pos]'h
      if !isNewline b && !isLetter b && !isDigit b then pos + 1 else pos
    else pos
  if hi : i₁ < n then
    let rec consumeUpper (i : Nat) : Nat :=
      if h : i < n then
        if isUpper (data[i]'h) then consumeUpper (i + 1)
        else i
      else i
    termination_by data.size - i
    let upperEnd := consumeUpper i₁
    if hLower : upperEnd < n then
      if !isLower (data[upperEnd]'hLower) then 0
      else
        let rec consumeLower (i : Nat) : Nat :=
          if h : i < n then
            if isLower (data[i]'h) then consumeLower (i + 1)
            else i
          else i
        termination_by data.size - i
        let wordEnd := consumeLower upperEnd
        let suffixLen := contractionSuffixLenAt data wordEnd
        (wordEnd + suffixLen) - pos
    else 0
  else 0

private def tryWordUpperSuffix (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  let i₁ : Nat :=
    if h : pos < n then
      let b := data[pos]'h
      if !isNewline b && !isLetter b && !isDigit b then pos + 1 else pos
    else pos
  if hi : i₁ < n then
    if !isUpper (data[i₁]'hi) then 0
    else
      let rec consumeUpper (i : Nat) : Nat :=
        if h : i < n then
          if isUpper (data[i]'h) then consumeUpper (i + 1)
          else i
        else i
      termination_by data.size - i
      let upperEnd := consumeUpper i₁
      let rec consumeLower (i : Nat) : Nat :=
        if h : i < n then
          if isLower (data[i]'h) then consumeLower (i + 1)
          else i
        else i
      termination_by data.size - i
      let wordEnd := consumeLower upperEnd
      let suffixLen := contractionSuffixLenAt data wordEnd
      (wordEnd + suffixLen) - pos
  else 0

-- ---------------------------------------------------------------------------
-- Branch 3: Digits  \p{N}{1,3}
-- ---------------------------------------------------------------------------

def tryDigits (data : ByteArray) (pos : Nat) : Nat :=
  if h0 : pos < data.size then
    if !isDigit (data[pos]'h0) then 0
    else
      let n  := data.size
      let i₁ := pos + 1
      let i₂ : Nat :=
        if h : i₁ < n then
          if isDigit (data[i₁]'h) then i₁ + 1 else i₁
        else i₁
      let i₃ : Nat :=
        if i₂ < pos + 3 then
          if h : i₂ < n then
            if isDigit (data[i₂]'h) then i₂ + 1 else i₂
          else i₂
        else i₂
      i₃ - pos
  else 0

-- ---------------------------------------------------------------------------
-- Branch 4: Punctuation  ' '?[^\s\p{L}\p{N}]++[\r\n]*
-- ---------------------------------------------------------------------------

def tryPunct (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  let i₁ : Nat :=
    if h : pos < n then
      if (data[pos]'h).toNat == 32 then pos + 1 else pos
    else pos
  if hi : i₁ < n then
    if !isPunct (data[i₁]'hi) then 0
    else
      let rec consumePunct (i : Nat) : Nat :=
        if h : i < n then
          if isPunct (data[i]'h) then consumePunct (i + 1)
          else i
        else i
      termination_by data.size - i
      let i₂ := consumePunct i₁
      let rec consumeNewlines (i : Nat) : Nat :=
        if h : i < n then
          if isNewline (data[i]'h) then consumeNewlines (i + 1)
          else i
        else i
      termination_by data.size - i
      (consumeNewlines i₂) - pos
  else 0

private def tryPunctO200k (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  let i₁ : Nat :=
    if h : pos < n then
      if (data[pos]'h).toNat == 32 then pos + 1 else pos
    else pos
  if hi : i₁ < n then
    if !isPunct (data[i₁]'hi) then 0
    else
      let rec consumePunct (i : Nat) : Nat :=
        if h : i < n then
          if isPunct (data[i]'h) then consumePunct (i + 1)
          else i
        else i
      termination_by data.size - i
      let i₂ := consumePunct i₁
      let rec consumeTail (i : Nat) : Nat :=
        if h : i < n then
          let b := data[i]'h
          if isNewline b || b.toNat == 47 then consumeTail (i + 1)
          else i
        else i
      termination_by data.size - i
      (consumeTail i₂) - pos
  else 0

-- ---------------------------------------------------------------------------
-- Branch 5: Newline-WS  \s*[\r\n]
-- ---------------------------------------------------------------------------

def tryNewlineWS (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  let rec endOfWS (i : Nat) : Nat :=
    if h : i < n then
      if isSpace (data[i]'h) then endOfWS (i + 1)
      else i
    else i
  termination_by data.size - i
  let wsEnd := endOfWS pos
  if wsEnd == pos then 0
  else
    let rec lastNewline (j : Nat) : Option Nat :=
      if hj : j < n then
        if isNewline (data[j]'hj) then some j
        else if j > pos then lastNewline (j - 1)
        else none
      else none
    termination_by j + 1
    match lastNewline (wsEnd - 1) with
    | none   => 0
    | some j => (j + 1) - pos

-- ---------------------------------------------------------------------------
-- Branch 6: Trailing-WS  \s+(?!\S)
-- ---------------------------------------------------------------------------

def tryTrailingWS (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  if h0 : pos < n then
    if !isSpace (data[pos]'h0) then 0
    else
      let rec endOfWS (i : Nat) : Nat :=
        if h : i < n then
          if isSpace (data[i]'h) then endOfWS (i + 1)
          else i
        else i
      termination_by data.size - i
      let wsEnd := endOfWS pos
      if wsEnd >= n then wsEnd - pos
      else
        let rec findBreak (j : Nat) : Nat :=
          if j <= pos then 0
          else if hj : j < n then
            if isSpace (data[j]'hj) then j - pos
            else findBreak (j - 1)
          else findBreak (j - 1)
        termination_by j
        findBreak (wsEnd - 1)
  else 0

-- ---------------------------------------------------------------------------
-- Branch 7: Other-WS  \s+
-- ---------------------------------------------------------------------------

def tryOtherWS (data : ByteArray) (pos : Nat) : Nat :=
  let n := data.size
  if h0 : pos < n then
    if !isSpace (data[pos]'h0) then 0
    else
      let rec go (i : Nat) : Nat :=
        if h : i < n then
          if isSpace (data[i]'h) then go (i + 1)
          else i
        else i
      termination_by data.size - i
      (go pos) - pos
  else 0

-- ---------------------------------------------------------------------------
-- Priority dispatch
-- ---------------------------------------------------------------------------

def nextTokenLen (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) : Nat :=
  match profile with
  | .cl100k =>
      let n1 := tryContraction data pos; if n1 != 0 then n1 else
      let n2 := tryWord data pos; if n2 != 0 then n2 else
      let n3 := tryDigits data pos; if n3 != 0 then n3 else
      let n4 := tryPunct data pos; if n4 != 0 then n4 else
      let n5 := tryNewlineWS data pos; if n5 != 0 then n5 else
      let n6 := tryTrailingWS data pos; if n6 != 0 then n6 else
      let n7 := tryOtherWS data pos; if n7 != 0 then n7 else
      1
  | .o200k =>
      let n1 := tryWordLowerSuffix data pos; if n1 != 0 then n1 else
      let n2 := tryWordUpperSuffix data pos; if n2 != 0 then n2 else
      let n3 := tryDigits data pos; if n3 != 0 then n3 else
      let n4 := tryPunctO200k data pos; if n4 != 0 then n4 else
      let n5 := tryNewlineWS data pos; if n5 != 0 then n5 else
      let n6 := tryTrailingWS data pos; if n6 != 0 then n6 else
      let n7 := tryOtherWS data pos; if n7 != 0 then n7 else
      1

theorem nextTokenLen_pos (profile : PreTokenizerProfile) (data : ByteArray) (pos : Nat) :
    1 ≤ nextTokenLen profile data pos := by
  cases profile <;> simp only [nextTokenLen, bne_iff_ne, ne_eq] <;> split_ifs <;> omega

-- ---------------------------------------------------------------------------
-- Main loop
-- ---------------------------------------------------------------------------

def preTokenizeASCII (profile : PreTokenizerProfile) (data : ByteArray) : Array ByteArray :=
  let rec loop (pos : Nat) (acc : Array ByteArray) : Array ByteArray :=
    if h : pos < data.size then
      let n      := nextTokenLen profile data pos
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
  loop 0 #[]

-- ---------------------------------------------------------------------------
-- Lemma 4 – partition
-- ---------------------------------------------------------------------------

-- Helper: foldl with push appends the new element
private lemma foldl_push_append (acc : Array ByteArray) (x : ByteArray) :
    (acc.push x).foldl (· ++ ·) ByteArray.empty =
    acc.foldl (· ++ ·) ByteArray.empty ++ x := by
  simp [Array.foldl_push]

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
