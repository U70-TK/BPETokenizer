import LeanBPETokenizer.Basic
import LeanBPETokenizer.ASCIIClassifiers
import LeanBPETokenizer.PreTokenizer
import LeanBPETokenizer.BPECore
import LeanBPETokenizer.WellFormed
import LeanBPETokenizer.Decompose
import LeanBPETokenizer.EncDec
import LeanBPETokenizer.RoundTrip
import LeanBPETokenizer.TokenizerJson

/-!
# LeanBPETokenizer

Top-level public interface for the ASCII BPE tokenizer library.

This module re-exports the proof and runtime bridge modules that make up the
package:

- `ASCIIClassifiers`: byte predicates and normalization lemmas
- `PreTokenizer`: ASCII pretokenization and regex-spec correspondence
- `BPECore`: merge and decode primitives
- `WellFormed`: construction-side invariants and `EncodeReady` builders
- `Decompose`: greedy decomposition correctness
- `EncDec`: chunk/text encode-decode correctness
- `RoundTrip`: end-to-end internal-id roundtrip theorems
- `TokenizerJson`: validated runtime loader and external-id roundtrip theorems

`Basic` remains a lightweight prelude hook for future shared definitions, but
the actual package interface lives here.
-/
