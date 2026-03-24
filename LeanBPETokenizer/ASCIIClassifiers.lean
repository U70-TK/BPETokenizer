import Mathlib.Tactic

/-!
# Part 1 – ASCII Character Classifiers

Pure decidable predicates on `UInt8` (byte values 0–255).
These mirror the Python helpers in `core.py` and are used by the
pre-tokenizer state machine in `PreTokenizer.lean`.

We access the underlying natural number via `UInt8.toNat`.
-/

namespace BPE

-- ---------------------------------------------------------------------------
-- Basic classifiers
-- ---------------------------------------------------------------------------

/-- A byte is ASCII iff its value is in 0..127. -/
def isASCII (b : UInt8) : Bool := b.toNat ≤ 127

/-- ASCII uppercase letters A–Z (65–90). -/
def isUpper (b : UInt8) : Bool := 65 ≤ b.toNat && b.toNat ≤ 90

/-- ASCII lowercase letters a–z (97–122). -/
def isLower (b : UInt8) : Bool := 97 ≤ b.toNat && b.toNat ≤ 122

/-- ASCII letter: A–Z or a–z. -/
def isLetter (b : UInt8) : Bool := isUpper b || isLower b

/-- ASCII digit: 0–9 (48–57). -/
def isDigit (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57

/-- ASCII whitespace: space(32), tab(9), LF(10), VT(11), FF(12), CR(13). -/
def isSpace (b : UInt8) : Bool :=
  b.toNat == 9 || b.toNat == 10 || b.toNat == 11 ||
  b.toNat == 12 || b.toNat == 13 || b.toNat == 32

/-- Newline characters: LF(10) or CR(13). -/
def isNewline (b : UInt8) : Bool := b.toNat == 10 || b.toNat == 13

/--
Punctuation: ASCII, not a letter, not a digit, not whitespace, and ≥ 32.
-/
def isPunct (b : UInt8) : Bool :=
  isASCII b && !isLetter b && !isDigit b && !isSpace b && 32 ≤ b.toNat

/-- Lowercase an ASCII byte; non-uppercase bytes pass through unchanged. -/
def toLower (b : UInt8) : UInt8 :=
  if isUpper b then b + 32 else b

-- ---------------------------------------------------------------------------
-- Simp lemmas connecting Bool functions to Nat predicates
-- ---------------------------------------------------------------------------

@[simp] theorem isASCII_iff (b : UInt8) :
    isASCII b = true ↔ b.toNat ≤ 127 := by
  simp [isASCII]

@[simp] theorem isUpper_iff (b : UInt8) :
    isUpper b = true ↔ 65 ≤ b.toNat ∧ b.toNat ≤ 90 := by
  simp [isUpper, Bool.and_eq_true]

@[simp] theorem isLower_iff (b : UInt8) :
    isLower b = true ↔ 97 ≤ b.toNat ∧ b.toNat ≤ 122 := by
  simp [isLower, Bool.and_eq_true]

@[simp] theorem isLetter_iff (b : UInt8) :
    isLetter b = true ↔
      (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) := by
  simp [isLetter, Bool.or_eq_true, isUpper_iff, isLower_iff]

@[simp] theorem isDigit_iff (b : UInt8) :
    isDigit b = true ↔ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  simp [isDigit, Bool.and_eq_true]

@[simp] theorem isNewline_iff (b : UInt8) :
    isNewline b = true ↔ b.toNat = 10 ∨ b.toNat = 13 := by
  simp [isNewline, Bool.or_eq_true]

@[simp] theorem isSpace_iff (b : UInt8) :
    isSpace b = true ↔
      b.toNat = 9 ∨ b.toNat = 10 ∨ b.toNat = 11 ∨
      b.toNat = 12 ∨ b.toNat = 13 ∨ b.toNat = 32 := by
  simp only [isSpace, Bool.or_eq_true, beq_iff_eq]
  constructor <;> intro h
  · rcases h with (((((h | h) | h) | h) | h) | h) <;> simp [h]
  · rcases h with (h | h | h | h | h | h) <;>
    [exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))));
     exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))));
     exact Or.inl (Or.inl (Or.inl (Or.inr h)));
     exact Or.inl (Or.inl (Or.inr h));
     exact Or.inl (Or.inr h);
     exact Or.inr h]

-- ---------------------------------------------------------------------------
-- Negation simp lemmas
-- ---------------------------------------------------------------------------

@[simp] theorem isLetter_false_iff (b : UInt8) :
    isLetter b = false ↔
      ¬(65 ≤ b.toNat ∧ b.toNat ≤ 90) ∧ ¬(97 ≤ b.toNat ∧ b.toNat ≤ 122) := by
  constructor
  · intro h
    simp only [Bool.eq_false_iff, ne_eq, isLetter_iff, not_or] at h
    exact h
  · intro ⟨h1, h2⟩
    simp only [Bool.eq_false_iff, ne_eq, isLetter_iff, not_or]
    exact ⟨h1, h2⟩

@[simp] theorem isNewline_false_iff (b : UInt8) :
    isNewline b = false ↔ b.toNat ≠ 10 ∧ b.toNat ≠ 13 := by
  constructor
  · intro h
    simp only [Bool.eq_false_iff, ne_eq, isNewline_iff, not_or] at h
    exact h
  · intro ⟨h1, h2⟩
    simp only [Bool.eq_false_iff, ne_eq, isNewline_iff, not_or]
    exact ⟨h1, h2⟩

-- ---------------------------------------------------------------------------
-- Derived lemmas
-- ---------------------------------------------------------------------------

/-- Every newline byte is also a space byte. -/
theorem newline_imp_space (b : UInt8) (h : isNewline b = true) : isSpace b = true := by
  simp only [isNewline_iff] at h
  simp only [isSpace_iff]
  rcases h with h | h <;> omega

/-- Letter bytes are not newlines. -/
theorem letter_not_newline (b : UInt8) (h : isLetter b = true) : isNewline b = false := by
  simp only [isLetter_iff] at h
  simp only [isNewline_false_iff]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Digit bytes are not newlines. -/
theorem digit_not_newline (b : UInt8) (h : isDigit b = true) : isNewline b = false := by
  simp only [isDigit_iff] at h
  simp only [isNewline_false_iff]
  omega

/-- Letter bytes are not digits. -/
theorem letter_not_digit (b : UInt8) (h : isLetter b = true) : isDigit b = false := by
  simp only [isLetter_iff] at h
  simp only [Bool.eq_false_iff, ne_eq, isDigit_iff, not_and, Nat.not_le]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Digit bytes are not letters. -/
theorem digit_not_letter (b : UInt8) (h : isDigit b = true) : isLetter b = false := by
  simp only [isDigit_iff] at h
  simp only [isLetter_false_iff, not_and, Nat.not_le]
  omega

-- ---------------------------------------------------------------------------
-- toLower lemmas
-- ---------------------------------------------------------------------------

/-- toLower on a non-upper byte is identity. -/
@[simp] theorem toLower_non_upper (b : UInt8) (h : isUpper b = false) :
    toLower b = b := by
  simp [toLower, h]

/-- Key arithmetic lemma: `b.toNat + 32 < 256` when `b.toNat ≤ 90`. -/
private lemma upper_no_overflow (b : UInt8) (h : isUpper b = true) :
    b.toNat + 32 < 256 := by
  simp only [isUpper_iff] at h; omega

/-- `(b + 32 : UInt8).toNat = b.toNat + 32` when `b` is uppercase. -/
theorem toLower_upper_toNat (b : UInt8) (h : isUpper b = true) :
    (b + 32).toNat = b.toNat + 32 := by
  have hov := upper_no_overflow b h
  -- UInt8.toNat_add : (a + b).toNat = (a.toNat + b.toNat) % UInt8.size
  rw [UInt8.toNat_add]
  simp [UInt8.size]
  omega

/-- `isUpper (b + 32) = false` when `isUpper b = true` (no wraparound). -/
private theorem upper_add32_not_upper (b : UInt8) (h : isUpper b = true) :
    isUpper (b + 32) = false := by
  -- establish (b + 32).toNat = b.toNat + 32
  have key := toLower_upper_toNat b h
  rw [Bool.eq_false_iff]
  intro hcontra
  rw [isUpper_iff, key] at hcontra
  simp only [isUpper_iff] at h
  omega

/-- toLower of an upper byte is lowercase. -/
theorem toLower_upper_is_lower (b : UInt8) (h : isUpper b = true) :
    isLower (toLower b) = true := by
  simp only [toLower, h, ite_true, isLower_iff]
  rw [toLower_upper_toNat b h]
  simp only [isUpper_iff] at h
  omega

/-- toLower is idempotent. -/
theorem toLower_idempotent (b : UInt8) : toLower (toLower b) = toLower b := by
  unfold toLower
  by_cases h : isUpper b = true
  · -- isUpper b = true: toLower b = b + 32, then b + 32 is not uppercase
    simp [h, upper_add32_not_upper b h]
  · -- isUpper b = false: toLower b = b
    have h' : isUpper b = false := Bool.eq_false_iff.mpr h
    simp [h']

end BPE
