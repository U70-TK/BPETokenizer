# LeanBPETokenizer Proof Map

This folder contains the proof-carrying core of the ASCII-only BPE tokenizer.
The top-level interface is [../LeanBPETokenizer.lean](../LeanBPETokenizer.lean).

`Basic.lean` is not logically required by the current development. It is only a
lightweight prelude / extension hook. The real public interface is
`LeanBPETokenizer.lean`.

## Proof Ladder To The Final Roundtrip Theorem

The theorems compose in this order:

1. `ASCIIClassifiers.lean` proves the byte-level facts used by the
   pretokenizer.
2. `PreTokenizer.lean` proves the tokenizer split is faithful to the supported
   ASCII `cl100k` / `o200k` pattern and that the chunks re-concatenate to the
   original bytes.
3. `BPECore.lean` proves that merge steps preserve decoded bytes and decrease
   length when they fire.
4. `Decompose.lean` proves greedy decomposition preserves the original bytes.
5. `WellFormed.lean` proves that a valid merge list builds an `EncodeReady`
   tokenizer.
6. `EncDec.lean` proves one chunk roundtrips through encode/decode, then lifts
   that preservation across whole encodings.
7. `RoundTrip.lean` combines chunk roundtrip, chunk partition, and ASCII UTF-8
   roundtrip into the final internal-id theorem.
8. `TokenizerJson.lean` proves that a runtime-validated loaded tokenizer
   satisfies the hypotheses of the core theorem and therefore roundtrips
   external ids.

The core endpoint is:

- `ascii_bpe_roundtrip_withProfile`
  Math: `decode vocab inv (encodeWithProfile profile merges vocab shuffle s) = s`

The validated-loader endpoint is:

- `roundtripExternal_ok_of_loadedAsciiSound`
  Math: `roundtripExternal tok s = ok s`

## `ASCIIClassifiers.lean`

- `isASCII_iff`: proves the boolean ASCII classifier is exactly the numeric
  bound. Math: `isASCII b = true ↔ b.toNat ≤ 127`.
- `isUpper_iff`: proves uppercase detection is exactly the range `65..90`.
  Math: `isUpper b = true ↔ 65 ≤ b.toNat ∧ b.toNat ≤ 90`.
- `isLower_iff`: proves lowercase detection is exactly the range `97..122`.
  Math: `isLower b = true ↔ 97 ≤ b.toNat ∧ b.toNat ≤ 122`.
- `isLetter_iff`: proves letter detection is uppercase-or-lowercase.
  Math: `isLetter b = true ↔ upper(b) ∨ lower(b)`.
- `isDigit_iff`: proves digit detection is exactly the range `48..57`.
  Math: `isDigit b = true ↔ 48 ≤ b.toNat ∧ b.toNat ≤ 57`.
- `isNewline_iff`: proves newline detection is exactly LF or CR.
  Math: `isNewline b = true ↔ b.toNat = 10 ∨ b.toNat = 13`.
- `isSpace_iff`: proves space detection is exactly the supported ASCII
  whitespace set. Math: `isSpace b = true ↔ b.toNat ∈ {9,10,11,12,13,32}`.
- `isLetter_false_iff`: characterizes non-letters.
  Math: `isLetter b = false ↔ ¬upper(b) ∧ ¬lower(b)`.
- `isNewline_false_iff`: characterizes non-newlines.
  Math: `isNewline b = false ↔ b.toNat ≠ 10 ∧ b.toNat ≠ 13`.
- `newline_imp_space`: every newline is a space.
  Math: `isNewline b = true → isSpace b = true`.
- `letter_not_newline`: letters are not newlines.
  Math: `isLetter b = true → isNewline b = false`.
- `digit_not_newline`: digits are not newlines.
  Math: `isDigit b = true → isNewline b = false`.
- `letter_not_digit`: letters are not digits.
  Math: `isLetter b = true → isDigit b = false`.
- `digit_not_letter`: digits are not letters.
  Math: `isDigit b = true → isLetter b = false`.
- `toLower_non_upper`: `toLower` is identity off uppercase bytes.
  Math: `isUpper b = false → toLower b = b`.
- `upper_no_overflow`: uppercase bytes can safely add `32` in `UInt8`.
  Math: `isUpper b = true → b.toNat + 32 < 256`.
- `toLower_upper_toNat`: lowering an uppercase byte adds `32` on naturals.
  Math: `isUpper b = true → (b + 32).toNat = b.toNat + 32`.
- `upper_add32_not_upper`: an uppercase byte stops being uppercase after
  adding `32`. Math: `isUpper b = true → isUpper (b + 32) = false`.
- `toLower_upper_is_lower`: lowering an uppercase byte yields lowercase.
  Math: `isUpper b = true → isLower (toLower b) = true`.
- `toLower_idempotent`: lowercasing twice is the same as once.
  Math: `toLower (toLower b) = toLower b`.

## `PreTokenizer.lean`

- `le_consumeWs`: whitespace consumption is monotone.
  Math: `pos ≤ consumeWs data pos`.
- `lt_endOfWsRun_of_space`: if the current byte is whitespace, the current
  position is strictly inside the whitespace run.
  Math: `isSpace(data[pos]) = true → pos < endOfWsRun data pos`.
- `trailingWsSpecLen_eq_otherWsSpecLen_or_prev`: trailing-whitespace length is
  either the full whitespace length or the preceding slice.
  Math: `trailingWsSpecLen = otherWsSpecLen ∨ trailingWsSpecLen = previous-run`.
- `trailingWsSpecLen_le_otherWsSpecLen`: trailing whitespace is never longer
  than ordinary whitespace.
  Math: `trailingWsSpecLen data pos ≤ otherWsSpecLen data pos`.
- `tryTrailingWS_eq_spec`: implementation matches the trailing-whitespace spec.
  Math: `tryTrailingWS data pos = trailingWsSpecLen data pos`.
- `tryOtherWS_eq_spec`: implementation matches the ordinary-whitespace spec.
  Math: `tryOtherWS data pos = otherWsSpecLen data pos`.
- `nextTokenLen_eq_spec`: implementation matches the full spec-level branch
  chooser. Math: `nextTokenLen profile data pos = nextTokenLenSpec profile data pos`.
- `trailingWsSpecLen_of_space`: if current byte is whitespace, trailing
  whitespace consumes a positive run.
  Math: `isSpace(data[pos]) = true → trailingWsSpecLen data pos > 0`.
- `otherWsSpecLen_of_space`: same for ordinary whitespace.
  Math: `isSpace(data[pos]) = true → otherWsSpecLen data pos > 0`.
- `nextTokenLen_pos`: every tokenizer step consumes at least one byte before
  EOF. Math: `pos < data.size → nextTokenLen profile data pos > 0`.
- `nextTokenLen_correspondence`: one-step pretokenizer behavior matches the
  supported ASCII pattern semantics.
  Math: `AsciiCorrespondsAt profile data pos`.
- `cl100k_nextTokenLen_correspondence`: specialization to `cl100k`.
  Math: `Cl100kAsciiCorrespondsAt data pos`.
- `o200k_nextTokenLen_correspondence`: specialization to `o200k`.
  Math: `O200kAsciiCorrespondsAt data pos`.
- `preTokenizeASCII_loop_toList_eq`: loop form and list form of pretokenization
  agree. Math: `loop(...).toList = preTokenizeASCIIList ...`.
- `preTokenizeASCIIList_correspondence`: the recursive list form follows the
  sequence-level correspondence spec.
  Math: `AsciiCorrespondsSeqFrom profile data pos (preTokenizeASCIIList ...)`.
- `preTokenize_correspondence`: full token sequence matches the supported ASCII
  step semantics. Math: `AsciiCorrespondsSeqFrom profile data 0 (preTokenizeASCII ... )`.
- `cl100k_preTokenize_correspondence`: specialization to `cl100k`.
  Math: `Cl100kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .cl100k data)`.
- `o200k_preTokenize_correspondence`: specialization to `o200k`.
  Math: `O200kAsciiCorrespondsSeqFrom data 0 (preTokenizeASCII .o200k data)`.
- `nextTokenLen_matches_supportedAsciiPattern`: explicit spec-facing wrapper for
  the one-step theorem. Math: `nextTokenLen = supportedAsciiPattern-step`.
- `preTokenize_matches_supportedAsciiPattern`: explicit spec-facing wrapper for
  the whole-sequence theorem. Math: `preTokenizeASCII = supportedAsciiPattern-sequence`.
- `cl100k_preTokenize_matches_supportedAsciiPattern`: explicit `cl100k`
  spec-facing sequence theorem.
  Math: `preTokenizeASCII .cl100k = cl100k-ASCII-spec`.
- `o200k_preTokenize_matches_supportedAsciiPattern`: explicit `o200k`
  spec-facing sequence theorem.
  Math: `preTokenizeASCII .o200k = o200k-ASCII-spec`.
- `foldl_push_append`: joining after a push is append by the pushed chunk.
  Math: `foldl(++, acc.push x) = foldl(++, acc) ++ x`.
- `preTokenize_partition`: pretokenized chunks re-concatenate to the input.
  Math: `foldl (++) ByteArray.empty (preTokenizeASCII profile data) = data`.

## `BPECore.lean`

- `getStatsAux_contains_imp`: a counted adjacent pair really occurs in the
  scanned suffix. Math: `pair ∈ getStatsAux ids → ∃ ... adjacent(pair, ids)`.
- `getStats_contains_implies_exists_adj`: a pair counted by `getStats` really
  occurs adjacent in the input.
  Math: `getStats ids[pair] > 0 → ∃ xs ys, ids = xs ++ [p0,p1] ++ ys`.
- `bpeMergeAux_preserves`: the auxiliary merge pass preserves any property
  already true of carried ids and untouched suffix ids.
  Math: `P(acc) ∧ P(xs) → P(bpeMergeAux pair idx acc xs)`.
- `bpeMerge_preserves`: the public merge pass preserves such a property.
  Math: `(∀ id ∈ ids, P id) → ∀ id ∈ bpeMerge ids pair idx, P id`.
- `decodeBytes_nil`: decoding an empty id list is empty.
  Math: `decodeBytes vocab [] = ε`.
- `decodeBytes_singleton`: decoding one id gives its vocab bytes.
  Math: `decodeBytes vocab [id] = vocab[id]`.
- `decodeBytesFrom_eq`: accumulator decoder equals the plain decoder.
  Math: `decodeBytesFrom vocab ε ids = decodeBytes vocab ids`.
- `decodeBytesFrom_step`: one-step accumulator equation.
  Math: `decodeBytesFrom vocab acc (id::ids) = ...`.
- `decodeBytesFrom_acc`: prepending to the accumulator prepends to the output.
  Math: `decodeBytesFrom vocab (base ++ acc) ids = base ++ decodeBytesFrom vocab acc ids`.
- `decodeBytesFrom_prepend`: specialized prepend form.
  Math: `decodeBytesFrom vocab (vocab[x] ++ acc) xs = vocab[x] ++ ...`.
- `decodeBytesFrom_append`: append law for the accumulator decoder.
  Math: `decodeBytesFrom vocab acc (xs ++ ys) = ...`.
- `decodeBytes_append`: decode distributes over append.
  Math: `decodeBytes vocab (xs ++ ys) = decodeBytes vocab xs ++ decodeBytes vocab ys`.
- `lemma6_decodeBytes_distributes`: named wrapper of `decodeBytes_append`.
  Math: same as `decodeBytes_append`.
- `bpeMergeAux_length`: merge pass never increases length.
  Math: `|bpeMergeAux pair idx acc xs| ≤ |acc| + |xs|`.
- `bpeMerge_length_le`: public merge pass is length non-increasing.
  Math: `|bpeMerge ids pair idx| ≤ |ids|`.
- `bpeMergeAux_length_lt`: if the pair fires, auxiliary merge strictly
  decreases length. Math: `fires(pair,xs) → |result| < |acc| + |xs|`.
- `bpeMerge_length_lt`: if the pair fires, public merge strictly decreases
  length. Math: `fires(pair,ids) → |bpeMerge ids pair idx| < |ids|`.
- `decodeBytes_cons'`: decode on a cons cell.
  Math: `decodeBytes vocab (x::xs) = vocab[x] ++ decodeBytes vocab xs`.
- `bpeMergeAux_decode_inv`: one auxiliary merge step preserves decoded bytes if
  the new id expands to the pair bytes.
  Math: `vocab[idx] = vocab[p0] ++ vocab[p1] → decode(result) = decode(input)`.
- `bpeMerge_decode_eq`: public merge preserves decoded bytes under the same
  concat hypothesis. Math: `vocab[idx] = vocab[p0] ++ vocab[p1] → decode(bpeMerge ids (p0,p1) idx) = decode ids`.

## `WellFormed.lean`

- `buildVocab_base`: `buildVocab` contains every base byte token.
  Math: `i < 256 → buildVocab mergeList[i] = [i]`.
- `lemma1_merge_preserves_decode`: a well-formed merge preserves decoded bytes.
  Math: `WellFormed → decode(bpeMerge ids pair idx) = decode(ids)`.
- `lemma2_shuffle_cancel`: inverse shuffle cancels shuffle on bytes.
  Math: `inverseShuffle (byteShuffle b) = b`.
- `shuffle_cancel_array`: inverse shuffle cancels shuffle pointwise on arrays.
  Math: `map inverseShuffle (map byteShuffle xs) = xs`.
- `foldl_ne_inserts_preserves_getD`: inserting other keys does not change a
  different lookup. Math: `k ∉ insertedKeys → getD after k = getD before k`.
- `base_fold_getD`: the initial base-token fold stores the singleton byte.
  Math: `baseFold[i] = [i]`.
- `foldl_merges_preserves_getD`: folding merges keeps previously-known entries.
  Math: `known k → getD after k = getD before k`.
- `buildVocab_base_token`: partial base-token correctness of `buildVocab`.
  Math: `i < 256 → buildVocab mergeList[i] = [i]`.
- `valid_target_ge`: valid merge targets are not base ids.
  Math: `ValidMergeList → 256 ≤ target`.
- `valid_targets_avoid_known`: valid targets are fresh relative to known ids.
  Math: `ValidMergeList → target ∉ knownIds`.
- `valid_pairs_avoid_known`: valid merge pairs reference already-known ids.
  Math: `ValidMergeList → p0,p1 ∈ knownIds`.
- `valid_dropPrefix`: validity is preserved on the tail when recursing.
  Math: `ValidMergeList (e::es) → ValidMergeList es`.
- `mem_entry_of_mem_map_fst`: membership in `List.map Prod.fst` comes from an
  original source entry. Math: `x ∈ map fst l → ∃ y, (x,y) ∈ l`.
- `valid_pairwise_keys`: valid merge targets are pairwise distinct.
  Math: `ValidMergeList → Pairwise (≠) targets`.
- `buildVocabFrom_preserves_known`: `buildVocabFrom` preserves known entries.
  Math: `known k → buildVocabFrom after[k] = before[k]`.
- `buildVocab_entry_decomp`: each inserted merge target decodes to its children
  concatenated. Math: `vocab[idx] = vocab[p0] ++ vocab[p1]`.
- `buildMerges_mem_of_lookup`: merge-map lookup comes from a source merge-list
  entry. Math: `buildMerges mergeList[(p0,p1)] = idx → ((p0,p1),idx) ∈ mergeList`.
- `valid_buildVocab_base_token`: `ValidMergeList` implies base-token
  correctness for `buildVocab`.
  Math: `ValidMergeList → i < 256 → buildVocab mergeList[i] = [i]`.
- `buildEncodeReady`: valid merge lists build the exact hypothesis needed by
  encoding. Math: `ValidMergeList mergeList → EncodeReady (buildMerges mergeList) (buildVocab mergeList)`.
- `buildEncodeReadyFromAssumptions`: same result from split-out assumptions.
  Math: `assumptions → EncodeReady merges vocab`.
- `emptyValidMergeList`: the empty merge list is valid.
  Math: `ValidMergeList []`.
- `emptyEncodeReady`: the empty merge list yields an `EncodeReady` tokenizer.
  Math: `EncodeReady (buildMerges []) (buildVocab [])`.

## `Decompose.lean`

- `mergeAt_size`: merging two adjacent parts reduces part count by one.
  Math: `|mergeAt parts i| = |parts| - 1`.
- `ba_empty_append`: left identity of byte-array append.
  Math: `ε ++ x = x`.
- `foldl_ba_acc`: folding with an initial accumulator is append by that
  accumulator. Math: `foldl (++) init arr = init ++ foldl (++) ε arr`.
- `foldl_ba_append`: folding over concatenated arrays distributes.
  Math: `foldl (++) ε (xs ++ ys) = foldl xs ++ foldl ys`.
- `foldl_ba_push`: folding after a push appends the pushed value.
  Math: `foldl (++) ε (arr.push x) = foldl arr ++ x`.
- `singleton_size`: singleton array size is one.
  Math: `|#[x]| = 1`.
- `getElem_eq_of_eq`: equal indices give equal lookup goals.
  Math: `i = j → arr[i] = arr[j]`.
- `getElem_singleton_eq`: singleton lookup returns the unique element.
  Math: `#[x][0] = x`.
- `array_extract_decompose`: array extraction decomposes the array into prefix,
  merged middle, suffix. Math: `parts = prefix ++ middle ++ suffix`.
- `foldl_ba_singleton`: folding a singleton byte-array array yields its member.
  Math: `foldl (++) ε #[x] = x`.
- `mergeAt_join`: merging two adjacent parts preserves the joined bytes.
  Math: `join(mergeAt parts i) = join(parts)`.
- `ba_append_singleton_push`: pushing a byte matches append by a singleton
  byte-array. Math: `push(acc,b) = acc ++ [b]`.
- `foldl_push_data`: folding pushed bytes reconstructs the corresponding byte
  array. Math: `foldl push acc l = acc ++ ByteArray.mk l`.
- `initial_join`: the initial decomposition already joins to the token.
  Math: `join(initialParts token) = token`.
- `lemma3_decompose_roundtrip`: greedy decomposition preserves bytes.
  Math: `join(decompose ranks token) = token`.

## `EncDec.lean`

- `lemma7_ascii_utf8_roundtrip`: ASCII strings roundtrip through UTF-8 bytes.
  Math: `ofUTF8(toUTF8(s)) = s`.
- `foldl_best_mem_candidates`: best-candidate selection returns one of the
  candidate pairs. Math: `best ∈ candidates ∨ best = default`.
- `filterMap_mem_merges`: filtering candidate pairs against the merge map only
  returns actual merge-map entries.
  Math: `x ∈ filterMap merges candidates → x ∈ merges`.
- `encodeChunkLoop_decode_inv`: one recursive chunk-encoding loop preserves
  decoded bytes. Math: `decode(loop ids) = decode(ids0)`.
- `encodeChunkLoop_preserves`: recursive chunk encoding preserves any property
  closed under base ids and merge targets.
  Math: `base ∧ merge-closed → ∀ id ∈ encodeChunkLoop ..., P id`.
- `ids0_decode_eq`: the initial byte ids decode back to the source chunk.
  Math: `decodeBytes vocab ids0 = chunk`.
- `chunkRoundtrip`: one pretokenized chunk roundtrips through encode/decode.
  Math: `decodeChunk vocab inv (encodeChunk merges vocab shuffle chunk) = chunk`.
- `encodeChunk_preserves`: encoded chunk ids satisfy any base-and-merge-closed
  predicate. Math: `∀ id ∈ encodeChunk ..., P id`.
- `encodeWithProfile_preserves`: whole-string encoding preserves such
  predicates.
  Math: `∀ id ∈ encodeWithProfile ..., P id`.
- `encode_preserves`: default `cl100k` wrapper for `encodeWithProfile_preserves`.
  Math: `∀ id ∈ encode ..., P id`.
- `chunkRoundtrip_of_wellFormed`: chunk roundtrip under `WellFormed`.
  Math: `WellFormed → decodeChunk(encodeChunk chunk) = chunk`.

## `RoundTrip.lean`

- `ascii_bpe_roundtrip_withProfile`: the main internal-id roundtrip theorem.
  Math: `decode vocab inv (encodeWithProfile profile merges vocab shuffle s) = s`.
- `ascii_bpe_roundtrip`: default `cl100k` wrapper around the main theorem.
  Math: `decode vocab inv (encode merges vocab shuffle s) = s`.
- `ascii_bpe_roundtrip_of_encodeReady_withProfile`: same main theorem with only
  `EncodeReady` rather than full `WellFormed`.
  Math: `EncodeReady merges vocab → decode(encodeWithProfile ...) = s`.
- `ascii_bpe_roundtrip_of_encodeReady`: default `cl100k` wrapper around the
  `EncodeReady` theorem.
  Math: `EncodeReady merges vocab → decode(encode ...) = s`.
- `ascii_bpe_roundtrip_of_valid_withProfile`: construction-facing theorem from a
  valid merge list.
  Math: `ValidMergeList mergeList → decode(buildVocab ... , encodeWithProfile(buildMerges ..., buildVocab ... , s)) = s`.
- `ascii_bpe_roundtrip_of_valid`: default `cl100k` wrapper around the valid
  merge-list theorem.
  Math: `ValidMergeList mergeList → decode(buildVocab ... , encode(buildMerges ..., buildVocab ... , s)) = s`.

## `TokenizerJson.lean`

- `internalIdMapped_of_validateInternalIdMap`: a successful boolean map check
  yields a two-way internal/external id witness.
  Math: `validateInternalIdMap tok i = true → ∃ e, intToExt(i)=e ∧ extToInt(e)=i`.
- `baseTokens_of_validateBaseTokens`: a successful base-token validator yields
  correct singleton-byte vocab entries.
  Math: `validateBaseTokens tok = true → vocab[i] = [i]` for `i < 256`.
- `mergeDecomp_of_validateMergeDecomp`: a successful merge-decomposition
  validator yields the concat property for every stored merge.
  Math: `validateMergeDecomp tok = true → vocab[idx] = vocab[p0] ++ vocab[p1]`.
- `encodeReady_of_validateEncodeReady`: runtime validation reflects into
  `EncodeReady`.
  Math: `validateEncodeReady tok = true → EncodeReady tok.merges tok.vocab`.
- `mergeTargetMapped_of_validateMergeTargetMaps`: successful merge-target map
  checks yield bidirectional id witnesses for merge targets.
  Math: `validateMergeTargetMaps tok = true → InternalIdMapped tok idx`.
- `idMapsSound_of_validateIdMaps`: id-map validation reflects into `IdMapsSound`.
  Math: `validateIdMaps tok = true → IdMapsSound tok`.
- `loadedAsciiSound_of_validate`: combined runtime validation yields the full
  proof object needed by the external theorem.
  Math: `validateLoadedAsciiTokenizer tok = true → LoadedAsciiSound tok`.
- `isAsciiString_eq_true_of_hascii`: propositional ASCII implies the runtime
  ASCII test succeeds. Math: `(∀ c ∈ s, c < 128) → isAsciiString s = true`.
- `loadedAsciiTokenizerSound_of_validate`: preferred public name for the same
  combined reflection theorem.
  Math: `validateLoadedAsciiTokenizer tok = true → LoadedAsciiSound tok`.
- `encodeDecodeIds_roundtrip`: translating internal ids to external ids and
  back is identity on mapped ids.
  Math: `mapped(ids) → decodeIds(encodeIds(ids)) = ok ids`.
- `roundtripExternal_ok_of_sound`: validated runtime tokenizers roundtrip at the
  external-id API boundary.
  Math: `LoadedAsciiSound tok → roundtripExternal tok s = ok s`.
- `roundtripExternal_ok_of_loadedAsciiSound`: preferred public name for the
  same external-id theorem.
  Math: `LoadedAsciiSound tok → roundtripExternal tok s = ok s`.

## Runtime Tests

The root-level `../Tests.lean` file is not part of the proof chain. It runs
packaged smoke tests over the supported JSON files, checks profile detection,
checks several ASCII roundtrips, compares Lean's external ids against a local
Python `tiktoken.Encoding` rebuilt from the same `tokenizer.json`, and checks
that non-ASCII input is rejected by the external-id API.
