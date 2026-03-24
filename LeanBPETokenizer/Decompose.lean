import LeanBPETokenizer.BPECore

/-!
# Part 5 – Token Decomposition (Lemma 3)

`decomposeToken` reconstructs the BPE sub-tokens of a given byte sequence
by greedily applying merges in rank order, starting from single bytes.

**Lemma 3 (decompose roundtrip)**:
  `(decomposeToken ranks token maxRank).foldl (· ++ ·) #[] = token`

The invariant `b"".join(parts) = token` is maintained at every iteration:
- Initially, `parts = [bytes([b]) | b ∈ token]` (trivially joins to `token`).
- Each step merges two adjacent parts into their concatenation, preserving join.
- Termination: the list length strictly decreases with each merge.
-/

namespace BPE

-- ---------------------------------------------------------------------------
-- Rank map
-- ---------------------------------------------------------------------------

/-- A rank map assigns a merge rank to every (multi-byte) vocabulary entry. -/
abbrev RankMap := Std.HashMap ByteArray Nat

-- ---------------------------------------------------------------------------
-- Single step: find the best (lowest-rank) adjacent pair to merge
-- ---------------------------------------------------------------------------

/--
Find the index of the adjacent pair in `parts` with the lowest merge rank
that is below `maxRank` (if provided).
Returns `none` if no eligible pair exists.
-/
def findBestMerge (ranks : RankMap) (parts : Array ByteArray)
    (maxRank : Option Nat) : Option Nat :=
  let n := parts.size
  if n < 2 then none
  else
    let rec go (i : Nat) (bestIdx : Option Nat) (bestRank : Nat) : Option Nat :=
      if h_ge : i + 1 >= n then bestIdx
      else
        have hi  : i < n     := by omega
        have hi1 : i + 1 < n := by omega
        let merged := parts[i]'hi ++ parts[i + 1]'hi1
        match ranks.get? merged with
        | none => go (i + 1) bestIdx bestRank
        | some r =>
            let eligible :=
              match maxRank with
              | none => true
              | some mr => r < mr
            if eligible && r < bestRank then
              go (i + 1) (some i) r
            else
              go (i + 1) bestIdx bestRank
    termination_by parts.size - i
    go 0 none (maxRank.getD 0 + 3)

-- ---------------------------------------------------------------------------
-- Single merge step
-- ---------------------------------------------------------------------------

/--
Perform one BPE merge at index `i` in `parts`:
replace `parts[i]` and `parts[i+1]` with their concatenation.
-/
def mergeAt (parts : Array ByteArray) (i : Nat) (h : i + 1 < parts.size) :
    Array ByteArray :=
  let merged := parts[i] ++ parts[i + 1]
  (parts.extract 0 i |>.push merged) ++ parts.extract (i + 2) parts.size

/-- `mergeAt` reduces the length by exactly 1. -/
lemma mergeAt_size (parts : Array ByteArray) (i : Nat) (h : i + 1 < parts.size) :
    (mergeAt parts i h).size = parts.size - 1 := by
  simp [mergeAt, Array.size_append, Array.size_extract, Array.size_push]
  omega

/-- ByteArray.empty ++ x = x -/
private lemma ba_empty_append (x : ByteArray) : ByteArray.empty ++ x = x := by
  simp [ByteArray.ext_iff, ByteArray.data_append, ByteArray.data_empty]

/-- foldl (· ++ ·) with arbitrary accumulator equals acc ++ foldl with empty. -/
private lemma foldl_ba_acc (arr : Array ByteArray) (init : ByteArray) :
    arr.foldl (· ++ ·) init = init ++ arr.foldl (· ++ ·) ByteArray.empty := by
  simp only [← Array.foldl_toList]
  generalize arr.toList = l
  induction l generalizing init with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons, ba_empty_append]
      rw [ih (init ++ x), ih x, ByteArray.append_assoc]

/-- join (foldl (· ++ ·) ∅) distributes over array append. -/
private lemma foldl_ba_append (xs ys : Array ByteArray) :
    (xs ++ ys).foldl (· ++ ·) ByteArray.empty =
    xs.foldl (· ++ ·) ByteArray.empty ++ ys.foldl (· ++ ·) ByteArray.empty := by
  rw [Array.foldl_append, foldl_ba_acc ys]

/-- join of push appends the new element. -/
private lemma foldl_ba_push (arr : Array ByteArray) (x : ByteArray) :
    (arr.push x).foldl (· ++ ·) ByteArray.empty =
    arr.foldl (· ++ ·) ByteArray.empty ++ x := by
  simp [Array.foldl_push]

/-- Singleton array has size 1. -/
private lemma singleton_size (x : ByteArray) : #[x].size = 1 := rfl

/-- Array element access at equal indices gives equal results. -/
private lemma getElem_eq_of_eq (arr : Array ByteArray) {i j : Nat} (h : i = j)
    (hi : i < arr.size) (hj : j < arr.size) : arr[i]'hi = arr[j]'hj := by
  subst h; rfl

/-- Accessing a singleton array always returns the unique element. -/
private lemma getElem_singleton_eq (x : ByteArray) (k : Nat)
    (hk : k < (#[x] : Array ByteArray).size) :
    (#[x] : Array ByteArray)[k]'hk = x := by
  have hk0 : k = 0 := by
    have : (#[x] : Array ByteArray).size = 1 := rfl
    omega
  subst hk0; rfl

/-- Array decomposition: extracting around positions i and i+1. -/
private lemma array_extract_decompose (parts : Array ByteArray) (i : Nat)
    (h : i + 1 < parts.size) :
    parts.extract 0 i ++ #[parts[i]] ++ #[parts[i + 1]'h] ++
    parts.extract (i + 2) parts.size = parts := by
  have hi : i < parts.size := by omega
  have hsi  : #[parts[i]].size = 1 := rfl
  have hsi1 : #[parts[i + 1]'h].size = 1 := rfl
  apply Array.ext
  · -- Size equality
    simp only [Array.size_append, Array.size_extract, hsi, hsi1, Nat.min_def]
    split_ifs <;> omega
  · intro j _ hj
    have hjs : j < parts.size := hj
    -- Case split on which region j falls in
    simp only [Array.getElem_append, Array.getElem_extract, Array.size_append,
               Array.size_extract, hsi, hsi1, Nat.min_def]
    split_ifs with h1 h2 h3 h4 h5 h6 h7
    all_goals (first | rfl | omega | (apply getElem_eq_of_eq; omega) |
               (rw [getElem_singleton_eq]; apply getElem_eq_of_eq; omega))

/-- join of a singleton array is just the element. -/
private lemma foldl_ba_singleton (x : ByteArray) :
    #[x].foldl (· ++ ·) ByteArray.empty = x := by
  simp [Array.foldl_push, Array.foldl_empty]

/-- `mergeAt` preserves the join of all parts. -/
lemma mergeAt_join (parts : Array ByteArray) (i : Nat) (h : i + 1 < parts.size) :
    (mergeAt parts i h).foldl (· ++ ·) ByteArray.empty =
    parts.foldl (· ++ ·) ByteArray.empty := by
  have hdecomp := array_extract_decompose parts i h
  -- Unfold mergeAt and simplify LHS
  simp only [mergeAt, foldl_ba_append, foldl_ba_push]
  -- Use `set` to name extracted pieces; afterwards `parts` appears only in `J parts` (RHS)
  set pre := parts.extract 0 i
  set suf := parts.extract (i + 2) parts.size
  set pi  := parts[i]
  set pi1 := parts[i + 1]'h
  -- hdecomp is now: pre ++ #[pi] ++ #[pi1] ++ suf = parts
  -- Goal: J pre ++ (pi ++ pi1) ++ J suf = J parts
  -- `parts` appears only on the RHS now, so rw [← hdecomp] is safe
  rw [← hdecomp, foldl_ba_append, foldl_ba_append, foldl_ba_append,
      foldl_ba_singleton, foldl_ba_singleton]
  simp [ByteArray.append_assoc]

-- ---------------------------------------------------------------------------
-- decomposeToken
-- ---------------------------------------------------------------------------

/--
BPE decomposition: split `token` into sub-tokens using `ranks`.

Starts with the token split into individual bytes, then greedily merges
adjacent pairs in lowest-rank-first order, up to (but not including)
`maxRank`.

This mirrors `decompose_token` in `core.py`.
-/
def decomposeToken (ranks : RankMap) (token : ByteArray)
    (maxRank : Option Nat := none) : Array ByteArray :=
  -- initialise: split into single bytes (map over the raw byte array)
  let initial : Array ByteArray :=
    token.data.map (fun b => ByteArray.mk #[b])
  -- iteratively merge
  let rec loop (parts : Array ByteArray) : Array ByteArray :=
    match findBestMerge ranks parts maxRank with
    | none => parts  -- no more eligible merges
    | some i =>
        if h : i + 1 < parts.size then
          loop (mergeAt parts i h)
        else
          parts  -- shouldn't happen if findBestMerge is correct
  termination_by parts.size
  decreasing_by
    have := mergeAt_size parts i h
    omega
  loop initial

-- ---------------------------------------------------------------------------
-- Lemma 3 – Decompose Roundtrip
-- ---------------------------------------------------------------------------

/-- `acc ++ ByteArray.mk #[b] = acc.push b` -/
private lemma ba_append_singleton_push (acc : ByteArray) (b : UInt8) :
    acc ++ ByteArray.mk #[b] = acc.push b := by
  simp [ByteArray.ext_iff, ByteArray.data_append, ByteArray.data_push, Array.append_singleton]

/-- `(l.foldl ByteArray.push acc).data = acc.data ++ l.toArray` -/
private lemma foldl_push_data (l : List UInt8) (acc : ByteArray) :
    (l.foldl ByteArray.push acc).data = acc.data ++ l.toArray := by
  induction l generalizing acc with
  | nil => simp [Array.append_empty]
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc.push b), ByteArray.data_push,
          show acc.data.push b = acc.data ++ #[b] from (Array.append_singleton ..).symm,
          Array.append_assoc]
      congr 1
      apply Array.ext'
      simp [List.toList_toArray]

/-- The initial single-byte split joins back to the original token. -/
lemma initial_join (token : ByteArray) :
    let initial := token.data.map (fun b => ByteArray.mk #[b])
    initial.foldl (· ++ ·) ByteArray.empty = token := by
  simp only
  rw [Array.foldl_map, ← Array.foldl_toList]
  simp_rw [ba_append_singleton_push]
  apply ByteArray.ext_iff.mpr
  rw [foldl_push_data, ByteArray.data_empty, Array.empty_append, List.toList_toArray]

/--
**Lemma 3 (Decompose Roundtrip)**:
The parts produced by `decomposeToken` join back to the original token.

Proof:
- **Invariant**: at every call to `loop parts`, `parts.foldl (· ++ ·) ∅ = token`.
- **Base**: established by `initial_join`.
- **Step**: `mergeAt_join` shows the invariant is preserved.
- **Termination**: `mergeAt_size` shows the list shrinks.
-/
theorem lemma3_decompose_roundtrip (ranks : RankMap) (token : ByteArray)
    (maxRank : Option Nat) :
    (decomposeToken ranks token maxRank).foldl (· ++ ·) ByteArray.empty = token := by
  -- Prove: for all n and parts of size ≤ n satisfying the join invariant,
  -- the loop produces a result also satisfying the invariant.
  suffices key : ∀ (n : Nat) (parts : Array ByteArray),
      parts.size ≤ n →
      parts.foldl (· ++ ·) ByteArray.empty = token →
      (decomposeToken.loop ranks maxRank parts).foldl (· ++ ·) ByteArray.empty = token by
    simp only [decomposeToken]
    exact key _ _ le_rfl (initial_join token)
  intro n
  induction n with
  | zero =>
      intro parts hsize hinv
      have hn0 : parts.size = 0 := Nat.le_zero.mp hsize
      -- findBestMerge returns none since parts.size < 2
      have hfind : findBestMerge ranks parts maxRank = none := by
        simp [findBestMerge, show parts.size < 2 by omega]
      have hloop : decomposeToken.loop ranks maxRank parts = parts := by
        conv_lhs => rw [decomposeToken.loop.eq_1]
        simp only [hfind]
      rw [hloop]; exact hinv
  | succ n ih =>
      intro parts hsize hinv
      cases h_fbm : findBestMerge ranks parts maxRank with
      | none =>
          have hloop : decomposeToken.loop ranks maxRank parts = parts := by
            conv_lhs => rw [decomposeToken.loop.eq_1]
            simp only [h_fbm]
          rw [hloop]; exact hinv
      | some i =>
          have hloop : decomposeToken.loop ranks maxRank parts =
              if hb : i + 1 < parts.size then
                decomposeToken.loop ranks maxRank (mergeAt parts i hb)
              else parts := by
            conv_lhs => rw [decomposeToken.loop.eq_1]
            simp only [h_fbm]
          rw [hloop]
          split_ifs with hb
          · apply ih (mergeAt parts i hb)
            · have := mergeAt_size parts i hb; omega
            · rw [mergeAt_join]; exact hinv
          · exact hinv

end BPE
