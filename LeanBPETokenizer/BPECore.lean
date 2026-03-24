import LeanBPETokenizer.ASCIIClassifiers

/-!
# Part 3 – BPE Core Helpers

Pure functions for BPE encoding:
- `getStats`   : count consecutive pairs in a token-id list
- `bpeMerge`   : replace a pair with a new token id
- `decodeBytes`: concatenate vocab byte-strings for a list of ids

These mirror `_get_stats`, `_merge`, and `decode_bytes` in `core.py`.
-/

namespace BPE

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

/-- A token id is a natural number. -/
abbrev TokenId := Nat

/-- A vocabulary as a partial map (token id → bytes). -/
abbrev VocabMap := Std.HashMap TokenId ByteArray

/-- A merge table: pair of token ids → merged token id. -/
abbrev MergeMap := Std.HashMap (TokenId × TokenId) TokenId

-- ---------------------------------------------------------------------------
-- getStats
-- ---------------------------------------------------------------------------

/-- Inner loop for `getStats`: accumulates pair counts. -/
private def getStatsAux (xs : List TokenId) (acc : Std.HashMap (TokenId × TokenId) Nat) :
    Std.HashMap (TokenId × TokenId) Nat :=
  match xs with
  | [] | [_] => acc
  | a :: b :: rest =>
      getStatsAux (b :: rest) (acc.insert (a, b) ((acc.getD (a, b) 0) + 1))
termination_by xs.length

/--
Count consecutive adjacent pairs in `ids`.
Returns a map from pair to occurrence count.
-/
def getStats (ids : List TokenId) : Std.HashMap (TokenId × TokenId) Nat :=
  getStatsAux ids {}

-- ---------------------------------------------------------------------------
-- getStats: pair appearance lemma
-- ---------------------------------------------------------------------------

/-- Key helper: if `getStatsAux xs acc` contains `(p0, p1)` and `acc` did not,
    then `(p0, p1)` appears consecutively in `xs`. -/
private lemma getStatsAux_contains_imp
    (p0 p1 : TokenId) :
    ∀ (n : Nat) (xs : List TokenId) (acc : Std.HashMap (TokenId × TokenId) Nat),
    xs.length ≤ n → ¬acc.contains (p0, p1) →
    (getStatsAux xs acc).contains (p0, p1) →
    ∃ ys zs, xs = ys ++ [p0, p1] ++ zs := by
  intro n
  induction n with
  | zero =>
      intro xs acc hlen hneg hpos
      match xs with
      | [] =>
          simp [getStatsAux] at hpos
          exact absurd hpos hneg
      | [_] => simp at hlen
      | _ :: _ :: _ => simp at hlen
  | succ n ih =>
      intro xs acc hlen hneg hpos
      match xs with
      | [] =>
          simp [getStatsAux] at hpos
          exact absurd hpos hneg
      | [_] =>
          simp [getStatsAux] at hpos
          exact absurd hpos hneg
      | a :: b :: rest =>
          simp only [getStatsAux] at hpos
          by_cases hab : (a, b) == (p0, p1)
          · -- (a, b) = (p0, p1): found the pair at the head
            simp only [beq_iff_eq, Prod.mk.injEq] at hab
            exact ⟨[], rest, by simp [hab.1, hab.2]⟩
          · -- (a, b) ≠ (p0, p1): (p0, p1) must appear later
            have hacc' : ¬(acc.insert (a, b) (acc.getD (a, b) 0 + 1)).contains (p0, p1) := by
              rw [Std.HashMap.contains_insert]
              simp [hab, hneg]
            have hlen' : (b :: rest).length ≤ n := by
              simp only [List.length_cons] at hlen ⊢; omega
            have ⟨ys, zs, heq⟩ := ih (b :: rest) _ hlen' hacc' hpos
            exact ⟨a :: ys, zs, by simp [List.cons_append, heq]⟩

/-- If `(p0, p1)` appears in `getStats ids`, it occurs consecutively in `ids`. -/
theorem getStats_contains_implies_exists_adj
    (ids : List TokenId) (p0 p1 : TokenId)
    (h : (getStats ids).contains (p0, p1)) :
    ∃ ys zs, ids = ys ++ [p0, p1] ++ zs :=
  getStatsAux_contains_imp p0 p1 ids.length ids {} le_rfl (by simp)
    (by simpa [getStats] using h)

-- ---------------------------------------------------------------------------
-- bpeMerge
-- ---------------------------------------------------------------------------

/-- Auxiliary loop for `bpeMerge`. Accumulates result in reverse. -/
private def bpeMergeAux (pair : TokenId × TokenId) (idx : TokenId) :
    List TokenId → List TokenId → List TokenId
  | [],        acc => acc.reverse
  | [x],       acc => (x :: acc).reverse
  | a :: b :: rest, acc =>
      if a == pair.1 && b == pair.2 then
        bpeMergeAux pair idx rest (idx :: acc)
      else
        bpeMergeAux pair idx (b :: rest) (a :: acc)
termination_by xs _ => xs.length

/--
Replace every non-overlapping occurrence of `pair` in `ids` with `idx`.
Processes left-to-right.
-/
def bpeMerge (ids : List TokenId) (pair : TokenId × TokenId) (idx : TokenId) :
    List TokenId :=
  bpeMergeAux pair idx ids []

-- ---------------------------------------------------------------------------
-- decodeBytes
-- ---------------------------------------------------------------------------

/--
Concatenate the byte representations of each token id according to `vocab`.
-/
def decodeBytes (vocab : VocabMap) (ids : List TokenId) : ByteArray :=
  ids.foldl (fun acc id => acc ++ vocab.getD id ByteArray.empty) ByteArray.empty

-- ---------------------------------------------------------------------------
-- Basic lemmas
-- ---------------------------------------------------------------------------

@[simp] lemma decodeBytes_nil (vocab : VocabMap) :
    decodeBytes vocab [] = ByteArray.empty := by simp [decodeBytes]

@[simp] lemma decodeBytes_singleton (vocab : VocabMap) (id : TokenId) :
    decodeBytes vocab [id] = vocab.getD id ByteArray.empty := by simp [decodeBytes]

-- ---------------------------------------------------------------------------
-- Lemma 6: decodeBytes distributes over list concatenation
-- ---------------------------------------------------------------------------

/-- Helper: `decodeBytes` with arbitrary initial accumulator. -/
private def decodeBytesFrom (vocab : VocabMap) (acc : ByteArray) (ids : List TokenId) :
    ByteArray :=
  ids.foldl (fun a id => a ++ vocab.getD id ByteArray.empty) acc

private lemma decodeBytesFrom_eq (vocab : VocabMap) (ids : List TokenId) :
    decodeBytes vocab ids = decodeBytesFrom vocab ByteArray.empty ids := rfl

-- These are library lemmas in Lean 4.27 Init.Data.ByteArray.Lemmas
private alias ba_append_assoc := ByteArray.append_assoc
private alias ba_append_empty := ByteArray.append_empty

/-- Single-step unfolding of `decodeBytesFrom`. -/
private lemma decodeBytesFrom_step (vocab : VocabMap) (acc : ByteArray) (id : TokenId)
    (rest : List TokenId) :
    decodeBytesFrom vocab acc (id :: rest) =
    decodeBytesFrom vocab (acc ++ vocab.getD id ByteArray.empty) rest := by
  simp [decodeBytesFrom, List.foldl_cons]

/-- Key lemma: prepending to the accumulator is the same as prepending to the result. -/
private lemma decodeBytesFrom_acc (vocab : VocabMap) (acc base : ByteArray)
    (ids : List TokenId) :
    decodeBytesFrom vocab (acc ++ base) ids =
    acc ++ decodeBytesFrom vocab base ids := by
  induction ids generalizing base acc with
  | nil => rfl
  | cons id rest ih =>
      rw [decodeBytesFrom_step, decodeBytesFrom_step, ba_append_assoc]
      exact ih acc (base ++ vocab.getD id ByteArray.empty)

/-- Prepend form: `decodeBytesFrom vocab acc ids = acc ++ decodeBytesFrom vocab ∅ ids`. -/
private lemma decodeBytesFrom_prepend (vocab : VocabMap) (acc : ByteArray)
    (ids : List TokenId) :
    decodeBytesFrom vocab acc ids = acc ++ decodeBytesFrom vocab ByteArray.empty ids := by
  have h := decodeBytesFrom_acc vocab acc ByteArray.empty ids
  rwa [ba_append_empty] at h

/-- `decodeBytesFrom` over concatenated lists. -/
private lemma decodeBytesFrom_append (vocab : VocabMap) (acc : ByteArray)
    (xs ys : List TokenId) :
    decodeBytesFrom vocab acc (xs ++ ys) =
    decodeBytesFrom vocab (decodeBytesFrom vocab acc xs) ys := by
  simp [decodeBytesFrom, List.foldl_append]

/-- `decodeBytes` distributes over list concatenation (Lemma 6). -/
theorem decodeBytes_append (vocab : VocabMap) (xs ys : List TokenId) :
    decodeBytes vocab (xs ++ ys) =
    decodeBytes vocab xs ++ decodeBytes vocab ys := by
  simp only [decodeBytesFrom_eq]
  rw [decodeBytesFrom_append]
  exact decodeBytesFrom_prepend vocab _ ys

/-- Alias: Lemma 6 stated explicitly. -/
theorem lemma6_decodeBytes_distributes (vocab : VocabMap) (xs ys : List TokenId) :
    decodeBytes vocab (xs ++ ys) =
    decodeBytes vocab xs ++ decodeBytes vocab ys :=
  decodeBytes_append vocab xs ys

-- ---------------------------------------------------------------------------
-- bpeMerge length lemma (used for termination of encodeChunk)
-- ---------------------------------------------------------------------------

/-- Auxiliary length bound: `bpeMergeAux` result fits in `xs.length + acc.length`. -/
private lemma bpeMergeAux_length (pair : TokenId × TokenId) (idx : TokenId)
    (xs acc : List TokenId) :
    (bpeMergeAux pair idx xs acc).length ≤ xs.length + acc.length := by
  suffices h : ∀ n (ys acc : List TokenId), ys.length ≤ n →
      (bpeMergeAux pair idx ys acc).length ≤ ys.length + acc.length from
    h xs.length xs acc (le_refl _)
  intro n
  induction n with
  | zero =>
      intro ys acc hlen
      match ys with
      | [] => simp [bpeMergeAux]
      | _ :: _ => simp at hlen
  | succ n ih =>
      intro ys acc hlen
      match ys with
      | [] => simp [bpeMergeAux]
      | [x] => simp [bpeMergeAux]
      | a :: b :: rest =>
          simp only [bpeMergeAux]
          split_ifs with hcond
          · have hrest : rest.length ≤ n := by simp at hlen; omega
            have := ih rest (idx :: acc) hrest
            simp at this ⊢; omega
          · have hbrest : (b :: rest).length ≤ n := by simp at hlen ⊢; omega
            have := ih (b :: rest) (a :: acc) hbrest
            simp at this ⊢; omega

/-- After a merge, the list is no longer than the original. -/
theorem bpeMerge_length_le (ids : List TokenId) (pair : TokenId × TokenId)
    (idx : TokenId) :
    (bpeMerge ids pair idx).length ≤ ids.length := by
  simp only [bpeMerge]
  have h := bpeMergeAux_length pair idx ids []
  simpa using h

-- ---------------------------------------------------------------------------
-- bpeMerge strict length decrease
-- ---------------------------------------------------------------------------

/-- When `pair` appears consecutively in `xs`, `bpeMergeAux` produces strictly fewer elements. -/
private lemma bpeMergeAux_length_lt
    (pair : TokenId × TokenId) (idx : TokenId) :
    ∀ (n : Nat) (xs acc : List TokenId), xs.length ≤ n →
    (∃ ys zs, xs = ys ++ [pair.1, pair.2] ++ zs) →
    (bpeMergeAux pair idx xs acc).length < xs.length + acc.length := by
  intro n
  induction n with
  | zero =>
      intro xs acc hlen ⟨ys, zs, h⟩
      have hlen2 : 2 ≤ xs.length := by
        rw [h]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      omega
  | succ n ih =>
      intro xs acc hlen ⟨ys, zs, h⟩
      cases ys with
      | nil =>
          -- xs = [] ++ [pair.1, pair.2] ++ zs = pair.1 :: pair.2 :: zs
          have hxs : [] ++ ([pair.1, pair.2] : List TokenId) ++ zs = pair.1 :: pair.2 :: zs := by
            simp
          rw [hxs] at h; subst h
          simp only [List.length_cons] at hlen
          -- One-step expansion: pair is at the head, so it fires immediately
          have hstep : bpeMergeAux pair idx (pair.1 :: pair.2 :: zs) acc =
              bpeMergeAux pair idx zs (idx :: acc) := by
            simp [bpeMergeAux, beq_self_eq_true]
          rw [hstep]
          have hbound := bpeMergeAux_length pair idx zs (idx :: acc)
          simp only [List.length_cons] at hbound ⊢; omega
      | cons a ys' =>
          cases ys' with
          | nil =>
              -- xs = (a :: []) ++ [pair.1, pair.2] ++ zs = a :: pair.1 :: pair.2 :: zs
              have hxs : xs = a :: pair.1 :: pair.2 :: zs := by
                rw [h]; simp [List.cons_append, List.nil_append]
              rw [hxs] at hlen ⊢
              simp only [List.length_cons] at hlen
              -- One-step expansion to avoid over-simplification
              have hstep : bpeMergeAux pair idx (a :: pair.1 :: pair.2 :: zs) acc =
                  if a == pair.1 && pair.1 == pair.2 then
                    bpeMergeAux pair idx (pair.2 :: zs) (idx :: acc)
                  else
                    bpeMergeAux pair idx (pair.1 :: pair.2 :: zs) (a :: acc) := by
                simp [bpeMergeAux]
              rw [hstep]
              split_ifs with hcond
              · -- pair (a, pair.1) matched; use length bound
                have hbound := bpeMergeAux_length pair idx (pair.2 :: zs) (idx :: acc)
                simp only [List.length_cons] at hbound ⊢; omega
              · -- no match; recurse with pair.1 :: pair.2 :: zs, pair still at head
                have hexists : ∃ ys' zs', pair.1 :: pair.2 :: zs = ys' ++ [pair.1, pair.2] ++ zs' :=
                    ⟨[], zs, by simp⟩
                have hlen' : (pair.1 :: pair.2 :: zs).length ≤ n := by
                    simp only [List.length_cons] at hlen ⊢; omega
                have hlt := ih (pair.1 :: pair.2 :: zs) (a :: acc) hlen' hexists
                simp only [List.length_cons] at hlt ⊢; omega
          | cons b ys'' =>
              -- xs = (a :: b :: ys'') ++ [pair.1, pair.2] ++ zs = a :: b :: (ys'' ++ ...)
              have hxs : xs = a :: b :: (ys'' ++ [pair.1, pair.2] ++ zs) := by
                rw [h]; simp [List.cons_append, List.append_assoc]
              rw [hxs] at hlen ⊢
              -- One-step expansion to control simp depth
              have hstep : bpeMergeAux pair idx (a :: b :: (ys'' ++ [pair.1, pair.2] ++ zs)) acc =
                  if a == pair.1 && b == pair.2 then
                    bpeMergeAux pair idx (ys'' ++ [pair.1, pair.2] ++ zs) (idx :: acc)
                  else
                    bpeMergeAux pair idx (b :: (ys'' ++ [pair.1, pair.2] ++ zs)) (a :: acc) := by
                simp [bpeMergeAux]
              rw [hstep]
              split_ifs with hcond
              · -- match at head (a, b); pair in (ys'' ++ [pair.1, pair.2] ++ zs) is irrelevant
                have hbound := bpeMergeAux_length pair idx (ys'' ++ [pair.1, pair.2] ++ zs) (idx :: acc)
                simp only [List.length_append, List.length_cons, List.length_nil] at hbound ⊢
                simp only [List.length_cons] at hlen; omega
              · -- no match: recurse on b :: (ys'' ++ [pair.1, pair.2] ++ zs)
                -- pair still appears there: (b :: ys'') ++ [pair.1, pair.2] ++ zs
                have hexists : ∃ ys' zs',
                    b :: (ys'' ++ [pair.1, pair.2] ++ zs) = ys' ++ [pair.1, pair.2] ++ zs' :=
                    ⟨b :: ys'', zs, by simp [List.cons_append]⟩
                have hlen' : (b :: (ys'' ++ [pair.1, pair.2] ++ zs)).length ≤ n := by
                    simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
                    omega
                have hlt := ih (b :: (ys'' ++ [pair.1, pair.2] ++ zs)) (a :: acc) hlen' hexists
                simp only [List.length_append, List.length_cons, List.length_nil] at hlt ⊢
                simp only [List.length_cons] at hlen; omega

/-- When `pair` appears consecutively in `ids`, `bpeMerge` strictly reduces the list length. -/
theorem bpeMerge_length_lt (ids : List TokenId) (pair : TokenId × TokenId) (idx : TokenId)
    (h : ∃ ys zs, ids = ys ++ [pair.1, pair.2] ++ zs) :
    (bpeMerge ids pair idx).length < ids.length := by
  simp only [bpeMerge]
  have := bpeMergeAux_length_lt pair idx ids.length ids [] le_rfl h
  simpa using this

-- ---------------------------------------------------------------------------
-- bpeMerge decode preservation (Lemma 1)
-- ---------------------------------------------------------------------------

private lemma decodeBytes_cons' (vocab : VocabMap) (x : TokenId) (xs : List TokenId) :
    decodeBytes vocab (x :: xs) =
    vocab.getD x ByteArray.empty ++ decodeBytes vocab xs := by
  have : x :: xs = [x] ++ xs := rfl
  rw [this, decodeBytes_append, decodeBytes_singleton]

/-- `bpeMergeAux` invariant: the join of the result equals the join of the reversed
accumulator concatenated with the join of the remaining input. -/
private lemma bpeMergeAux_decode_inv
    (vocab : VocabMap)
    (pair : TokenId × TokenId) (idx : TokenId)
    (hdecomp : vocab.getD idx ByteArray.empty =
               vocab.getD pair.1 ByteArray.empty ++ vocab.getD pair.2 ByteArray.empty)
    (xs acc : List TokenId) :
    decodeBytes vocab (bpeMergeAux pair idx xs acc) =
    decodeBytes vocab acc.reverse ++ decodeBytes vocab xs := by
  suffices h : ∀ n (xs acc : List TokenId), xs.length ≤ n →
      decodeBytes vocab (bpeMergeAux pair idx xs acc) =
      decodeBytes vocab acc.reverse ++ decodeBytes vocab xs from
    h xs.length xs acc le_rfl
  intro n
  induction n with
  | zero =>
      intro xs acc hlen
      cases xs with
      | nil => simp [bpeMergeAux]
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro xs acc hlen
      match xs with
      | [] => simp [bpeMergeAux]
      | [x] =>
          simp only [bpeMergeAux, List.reverse_cons, decodeBytes_append]
      | a :: b :: rest =>
          simp only [bpeMergeAux]
          split_ifs with hcond
          · have ha : a = pair.1 := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.1
            have hb : b = pair.2 := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
            rw [ih rest (idx :: acc) (by simp [List.length_cons] at hlen; omega)]
            rw [List.reverse_cons, decodeBytes_append, decodeBytes_singleton, hdecomp, ← ha, ← hb]
            rw [decodeBytes_cons' vocab a, decodeBytes_cons' vocab b]
            simp [ByteArray.append_assoc]
          · rw [ih (b :: rest) (a :: acc) (by simp [List.length_cons] at hlen ⊢; omega)]
            rw [List.reverse_cons, decodeBytes_append, decodeBytes_singleton,
                decodeBytes_cons' vocab a]
            simp [ByteArray.append_assoc]

/-- **Lemma 1**: `bpeMerge` preserves `decodeBytes` when the merged token's bytes
equal the concatenation of the component tokens' bytes. -/
theorem bpeMerge_decode_eq
    (vocab : VocabMap)
    (ids : List TokenId)
    (pair : TokenId × TokenId) (idx : TokenId)
    (hdecomp : vocab.getD idx ByteArray.empty =
               vocab.getD pair.1 ByteArray.empty ++ vocab.getD pair.2 ByteArray.empty) :
    decodeBytes vocab (bpeMerge ids pair idx) = decodeBytes vocab ids := by
  simp only [bpeMerge]
  have h := bpeMergeAux_decode_inv vocab pair idx hdecomp ids []
  simpa using h

end BPE
