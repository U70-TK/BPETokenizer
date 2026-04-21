import LeanBPETokenizer
import Lean.Data.Json.Parser

open Lean

namespace BPE

/-- Human-readable profile names for test and study output. -/
def formatProfileName (profile : PreTokenizerProfile) : String :=
  match profile with
  | .cl100k => "cl100k"
  | .o200k => "o200k"

/-- Expected tokenizer profile for known packaged tokenizer paths. -/
def expectedProfileForPath? (path : System.FilePath) : Option PreTokenizerProfile :=
  if path = "tokenizers/cl100k/tokenizer.json" then
    some .cl100k
  else if path = "tokenizers/o200k_harmony/tokenizer.json" then
    some .o200k
  else
    none

/-- Hand-written whitespace and control-character samples. -/
def whitespaceStressSamples : List String :=
  [ ""
  , " "
  , "  "
  , "   "
  , "\t"
  , "\t\t"
  , "\n"
  , "\n\n"
  , "\r"
  , "\r\n"
  , " \n"
  , "\n "
  , " \t "
  , "a "
  , " a"
  , "a  b"
  , "a\nb"
  , "a\r\nb"
  , "line1\nline2\nline3"
  , "\tindent\tblock"
  , " \n\n tail"
  , "head \n\n"
  ]

/-- Hand-written punctuation and structured-text samples. -/
def punctuationStressSamples : List String :=
  [ "!"
  , "!!"
  , "???"
  , "..."
  , "[]{}()<>"
  , "\"quoted\""
  , "'single-quoted'"
  , "a,b;c:d"
  , "x=y+z"
  , "foo/bar/baz"
  , "./relative/path"
  , "../up/one"
  , "C:/tmp/file.txt"
  , "user@example.com"
  , "https://example.com/a/b?x=1&y=2"
  , "{\"k\":\"v\"}"
  , "[1,2,3,4]"
  , "alpha|beta|gamma"
  , "name=value; secure=true"
  , "punctuation!!!??"
  , "/slashes/too"
  ]

/-- Hand-written lexical and numeric samples. -/
def lexicalStressSamples : List String :=
  [ "hello"
  , "HELLO"
  , "Hello"
  , "camelCaseToken"
  , "snake_case_token"
  , "Title Case Words"
  , "caps AND lower"
  , "UPPER lower Title"
  , "don't stop"
  , "I'm you're we'll they'd"
  , "mix'ed contractions"
  , "123"
  , "123 456 789"
  , "007 bond"
  , "1,024"
  , "3.14159"
  , "id=42"
  , "abc123xyz"
  , "HELLO/world"
  , "line1\nline2"
  ]

/-- Generated combinatorial ASCII stress corpus. -/
def generatedStressSamples : List String :=
  let prefixes :=
    [ ""
    , " "
    , "/"
    , "GET "
    , "x="
    , "("
    ]
  let bodies :=
    [ "hello"
    , "world"
    , "don't"
    , "snake_case"
    , "camelCase"
    , "UPPER"
    , "123"
    , "foo/bar"
    ]
  let suffixes :=
    [ ""
    , "!"
    , " / tail"
    , "\nnext"
    ]
  prefixes.foldr
    (fun pre acc =>
      bodies.foldr
        (fun body acc' =>
          (suffixes.map fun post => pre ++ body ++ post) ++ acc')
        acc)
    []

/-- Large built-in corpus used by packaged tests and empirical study mode. -/
def packagedRegressionSamples : List String :=
  regressionSamples ++
    whitespaceStressSamples ++
    punctuationStressSamples ++
    lexicalStressSamples ++
    generatedStressSamples

/-- Summary of an empirical comparison between Lean and Python `tiktoken`. -/
structure StudySummary where
  sampleCount : Nat
  roundtripPasses : Nat
  encodeAgreementPasses : Nat
  decodePythonPasses : Nat
  leanTokenTotal : Nat
  pythonTokenTotal : Nat
  encodeNanosTotal : Nat
  deriving Repr

def StudySummary.empty : StudySummary :=
  { sampleCount := 0
    roundtripPasses := 0
    encodeAgreementPasses := 0
    decodePythonPasses := 0
    leanTokenTotal := 0
    pythonTokenTotal := 0
    encodeNanosTotal := 0 }

/-- Summary of a pure tokenization-speed benchmark. -/
structure BenchmarkSummary where
  sampleCount : Nat
  tokenTotal : Nat
  encodeNanosTotal : Nat
  deriving Repr

def BenchmarkSummary.empty : BenchmarkSummary :=
  { sampleCount := 0
    tokenTotal := 0
    encodeNanosTotal := 0 }

structure WarmColdBenchmarkSummary where
  cold : BenchmarkSummary
  warm : BenchmarkSummary
  deriving Repr

private def appendFailure
    (failures : List String)
    (path : System.FilePath)
    (msg : String) : List String :=
  if failures.length < 25 then
    failures ++ [s!"[{path}] {msg}"]
  else
    failures

private def parseIdsLine (raw : String) : Except String (List TokenId) := do
  let text := raw.trimAscii.toString
  if text.isEmpty then
    pure []
  else
    let pieces := text.splitOn ","
    let rec go : List String → Except String (List TokenId)
      | [] => pure []
      | piece :: rest =>
          match piece.trimAscii.toString.toNat? with
          | some n => return n :: (← go rest)
          | none => throw s!"invalid token id '{piece}' in Python output"
    go pieces

private def samplesToJson (samples : List String) : String :=
  let elems := samples.map (fun s => Json.compress (.str s))
  "[" ++ String.intercalate "," elems ++ "]"

private def parsePythonBatchOutput (raw : String) : Except String (Array (List TokenId)) := do
  let json <- Json.parse raw
  let rows <- json.getArr?
  rows.mapM fun row => do
    let ids <- row.getArr?
    pure (← ids.toList.mapM Json.getNat?)

private def pythonTiktokenBatchEncode
    (path : System.FilePath)
    (samples : List String) : IO (Except String (Array (List TokenId))) :=
  IO.FS.withTempFile fun handle tmpPath => do
    handle.putStr (samplesToJson samples)
    handle.flush
    let out ← IO.Process.output
      { cmd := "python3"
        args := #["scripts/tiktoken_batch_encode.py", path.toString, tmpPath.toString] }
    if out.exitCode == 0 then
      pure <| parsePythonBatchOutput out.stdout
    else
      pure <| .error out.stderr.trimAscii.toString

private def dropTrailingCR (line : String) : String :=
  if line.endsWith "\r" then
    line.dropEnd 1 |>.toString
  else
    line

/-- Load a newline-delimited ASCII dataset for empirical study. -/
def loadStudySamples (path : System.FilePath) : IO (List String) := do
  let contents ← IO.FS.readFile path
  let lines := (contents.splitOn "\n").map dropTrailingCR
  match lines.reverse with
  | "" :: rest => pure rest.reverse
  | _ => pure lines

private def checkExpectedProfile
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (failures : List String) : List String :=
  match expectedProfileForPath? path with
  | some expected =>
      if tok.profile = expected then
        failures
      else
        appendFailure failures path
          s!"expected profile {formatProfileName expected}, got {formatProfileName tok.profile}"
  | none =>
      failures

private def checkAsciiRejection
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (failures : List String) : List String :=
  match encodeExternalIds tok "café" with
  | .error _ => failures
  | .ok ids =>
      appendFailure failures path s!"non-ASCII input unexpectedly encoded as {ids}"

private def updateSummaryForRoundtrip
    (summary : StudySummary)
    (tok : LoadedAsciiTokenizer)
    (sample : String)
    (failures : List String)
    (path : System.FilePath) : StudySummary × List String :=
  match roundtripExternal tok sample with
  | .ok decoded =>
      if decoded = sample then
        ({ summary with
            sampleCount := summary.sampleCount + 1
            roundtripPasses := summary.roundtripPasses + 1 }, failures)
      else
        ({ summary with sampleCount := summary.sampleCount + 1 },
          appendFailure failures path
            s!"roundtrip mismatch for {repr sample}: decoded {repr decoded}")
  | .error err =>
      ({ summary with sampleCount := summary.sampleCount + 1 },
        appendFailure failures path
          s!"roundtrip failed for {repr sample}: {err}")

private def compareExpectedIds
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (sample : String)
    (expectedIds : List TokenId)
    (summary : StudySummary)
    (failures : List String) : IO (StudySummary × List String) := do
  let startNs ← IO.monoNanosNow
  let actual := encodeExternalIds tok sample
  let stopNs ← IO.monoNanosNow
  let elapsedNs := stopNs - startNs
  let summary := { summary with encodeNanosTotal := summary.encodeNanosTotal + elapsedNs }
  match actual with
  | .error err =>
      pure
        ({ summary with pythonTokenTotal := summary.pythonTokenTotal + expectedIds.length },
        appendFailure failures path s!"Lean encode failed for {repr sample}: {err}")
  | .ok actualIds =>
      let summary := {
        summary with
          leanTokenTotal := summary.leanTokenTotal + actualIds.length
          pythonTokenTotal := summary.pythonTokenTotal + expectedIds.length
          encodeAgreementPasses :=
            summary.encodeAgreementPasses + (if actualIds = expectedIds then 1 else 0)
      }
      let failures :=
        if actualIds = expectedIds then
          failures
        else
          appendFailure failures path
            s!"encode mismatch for {repr sample}: Lean {actualIds}, Python {expectedIds}"
          match decodeExternalIds tok expectedIds with
          | .ok decoded =>
              if decoded = sample then
                pure
                  ({ summary with
                      decodePythonPasses := summary.decodePythonPasses + 1 }, failures)
              else
                pure (summary,
                  appendFailure failures path
                    s!"decode mismatch for Python ids on {repr sample}: decoded {repr decoded}")
          | .error err =>
          pure (summary,
            appendFailure failures path
              s!"Lean decode failed for Python ids on {repr sample}: {err}")

private partial def compareSamplesLoop
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (samples : List String)
    (expectedRows : List (List TokenId))
    (summary : StudySummary)
    (failures : List String) : IO (StudySummary × List String) := do
  match samples, expectedRows with
  | [], [] => pure (summary, failures)
  | sample :: samples', expected :: rows' =>
      let (summary, failures) := updateSummaryForRoundtrip summary tok sample failures path
      let (summary, failures) ← compareExpectedIds path tok sample expected summary failures
      compareSamplesLoop path tok samples' rows' summary failures
  | _, _ =>
      pure (summary,
        appendFailure failures path
          "Python batch output length did not match the number of samples")

/-- Run an empirical study for one loaded tokenizer against Python `tiktoken`. -/
def runTokenizerStudy
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (samples : List String) : IO (StudySummary × List String) := do
  let failures0 := checkExpectedProfile path tok []
  let failures1 := checkAsciiRejection path tok failures0
  let expected ← pythonTiktokenBatchEncode path samples
  match expected with
  | .error err =>
      pure (StudySummary.empty,
        appendFailure failures1 path s!"python tiktoken batch encode failed: {err}")
  | .ok rows =>
      compareSamplesLoop path tok samples rows.toList StudySummary.empty failures1

private def formatSeconds (nanos : Nat) : String :=
  let secs : Float := nanos.toFloat / 1000000000.0
  toString secs

private def formatTokensPerSec (tokens : Nat) (nanos : Nat) : String :=
  if nanos = 0 then
    "0"
  else
    let secs : Float := nanos.toFloat / 1000000000.0
    let rate : Float := tokens.toFloat / secs
    toString rate

def renderStudySummary (summary : StudySummary) : List String :=
  [ s!"samples: {summary.sampleCount}"
  , s!"roundtrip passes: {summary.roundtripPasses}/{summary.sampleCount}"
  , s!"encode agreement: {summary.encodeAgreementPasses}/{summary.sampleCount}"
  , s!"decode(Python ids) passes: {summary.decodePythonPasses}/{summary.sampleCount}"
  , s!"Lean token total: {summary.leanTokenTotal}"
  , s!"Python token total: {summary.pythonTokenTotal}"
  , s!"num_tokens: {summary.leanTokenTotal}"
  , s!"total_time: {formatSeconds summary.encodeNanosTotal}s"
  , s!"tokens_per_sec: {formatTokensPerSec summary.leanTokenTotal summary.encodeNanosTotal}"
  ]

private partial def benchmarkSamplesLoop
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (samples : List String)
    (summary : BenchmarkSummary)
    (failures : List String) : IO (BenchmarkSummary × List String) := do
  match samples with
  | [] => pure (summary, failures)
  | sample :: samples' =>
      let encoded := encodeExternalIds tok sample
      match encoded with
      | .error err =>
          benchmarkSamplesLoop path tok samples'
            { summary with
                sampleCount := summary.sampleCount + 1 }
            (appendFailure failures path
              s!"Lean encode failed for {repr sample}: {err}")
      | .ok ids =>
          benchmarkSamplesLoop path tok samples'
            { summary with
                sampleCount := summary.sampleCount + 1
                tokenTotal := summary.tokenTotal + ids.length }
            failures

/-- Benchmark one loaded tokenizer on a corpus without Python cross-checking. -/
def benchmarkTokenizer
    (path : System.FilePath)
    (tok : LoadedAsciiTokenizer)
    (samples : List String) : IO (BenchmarkSummary × List String) := do
  let failures0 := checkExpectedProfile path tok []
  let failures1 := checkAsciiRejection path tok failures0
  let startNs ← IO.monoNanosNow
  let (summary, failures) ← benchmarkSamplesLoop path tok samples BenchmarkSummary.empty failures1
  let stopNs ← IO.monoNanosNow
  pure ({ summary with encodeNanosTotal := stopNs - startNs }, failures)

def renderBenchmarkSummary (summary : BenchmarkSummary) : List String :=
  [ s!"samples: {summary.sampleCount}"
  , s!"num_tokens: {summary.tokenTotal}"
  , s!"total_time: {formatSeconds summary.encodeNanosTotal}s"
  , s!"tokens_per_sec: {formatTokensPerSec summary.tokenTotal summary.encodeNanosTotal}"
  ]

def renderWarmColdBenchmarkSummary (summary : WarmColdBenchmarkSummary) : List String :=
  let coldRate :=
    formatTokensPerSec summary.cold.tokenTotal summary.cold.encodeNanosTotal
  let warmRate :=
    formatTokensPerSec summary.warm.tokenTotal summary.warm.encodeNanosTotal
  [ s!"cold.samples: {summary.cold.sampleCount}"
  , s!"cold.num_tokens: {summary.cold.tokenTotal}"
  , s!"cold.total_time: {formatSeconds summary.cold.encodeNanosTotal}s"
  , s!"cold.tokens_per_sec: {coldRate}"
  , s!"warm.samples: {summary.warm.sampleCount}"
  , s!"warm.num_tokens: {summary.warm.tokenTotal}"
  , s!"warm.total_time: {formatSeconds summary.warm.encodeNanosTotal}s"
  , s!"warm.tokens_per_sec: {warmRate}"
  ]

/-- Run packaged tests over the built-in stress corpus. -/
def runPackagedTests (paths : List System.FilePath) : IO UInt32 := do
  let mut failures : List String := []
  for path in paths do
    let loaded ← loadCertifiedAsciiTokenizer path
    match loaded with
    | .error err =>
        failures := appendFailure failures path s!"load failed: {err}"
    | .ok ⟨tok, _⟩ =>
        IO.println s!"[{path}] profile={formatProfileName tok.profile}"
        let (summary, pathFailures) ← runTokenizerStudy path tok packagedRegressionSamples
        for line in renderStudySummary summary do
          IO.println s!"[{path}] {line}"
        failures := failures ++ pathFailures
  if failures.isEmpty then
    pure 0
  else
    for failure in failures do
      IO.eprintln failure
    pure 1

/-- Run an empirical study over a newline-delimited dataset file. -/
def runEmpiricalStudy
    (paths : List System.FilePath)
    (datasetPath : System.FilePath) : IO UInt32 := do
  let samples ← loadStudySamples datasetPath
  IO.println s!"dataset: {datasetPath}"
  IO.println s!"loaded samples: {samples.length}"
  let mut failures : List String := []
  for path in paths do
    let loaded ← loadCertifiedAsciiTokenizer path
    match loaded with
    | .error err =>
        failures := appendFailure failures path s!"load failed: {err}"
    | .ok ⟨tok, _⟩ =>
        IO.println s!"[{path}] profile={formatProfileName tok.profile}"
        let (summary, pathFailures) ← runTokenizerStudy path tok samples
        for line in renderStudySummary summary do
          IO.println s!"[{path}] {line}"
        failures := failures ++ pathFailures
  if failures.isEmpty then
    pure 0
  else
    for failure in failures do
      IO.eprintln failure
    pure 1

/-- Run a pure speed benchmark over a newline-delimited dataset file. -/
def runSpeedBenchmark
    (paths : List System.FilePath)
    (datasetPath : System.FilePath) : IO UInt32 := do
  let samples ← loadStudySamples datasetPath
  IO.println s!"dataset: {datasetPath}"
  IO.println s!"loaded samples: {samples.length}"
  let mut failures : List String := []
  for path in paths do
    let loaded ← loadCertifiedAsciiTokenizer path
    match loaded with
    | .error err =>
        failures := appendFailure failures path s!"load failed: {err}"
    | .ok ⟨tok, _⟩ =>
        IO.println s!"[{path}] profile={formatProfileName tok.profile}"
        let (summary, pathFailures) ← benchmarkTokenizer path tok samples
        for line in renderBenchmarkSummary summary do
          IO.println s!"[{path}] {line}"
        failures := failures ++ pathFailures
  if failures.isEmpty then
    pure 0
  else
    for failure in failures do
      IO.eprintln failure
    pure 1

/-- Run cold/warm speed benchmark over a newline-delimited dataset file. -/
def runWarmColdSpeedBenchmark
    (paths : List System.FilePath)
    (datasetPath : System.FilePath) : IO UInt32 := do
  let samples ← loadStudySamples datasetPath
  IO.println s!"dataset: {datasetPath}"
  IO.println s!"loaded samples: {samples.length}"
  let mut failures : List String := []
  for path in paths do
    let loaded ← loadCertifiedAsciiTokenizer path
    match loaded with
    | .error err =>
        failures := appendFailure failures path s!"load failed: {err}"
    | .ok ⟨tok, _⟩ =>
        IO.println s!"[{path}] profile={formatProfileName tok.profile}"
        let (coldSummary, coldFailures) ← benchmarkTokenizer path tok samples
        let (warmSummary, warmFailures) ← benchmarkTokenizer path tok samples
        let warmCold : WarmColdBenchmarkSummary :=
          { cold := coldSummary, warm := warmSummary }
        for line in renderWarmColdBenchmarkSummary warmCold do
          IO.println s!"[{path}] {line}"
        failures := failures ++ coldFailures ++ warmFailures
  if failures.isEmpty then
    pure 0
  else
    for failure in failures do
      IO.eprintln failure
    pure 1

end BPE
