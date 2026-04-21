import LeanBPETokenizer
import Tests

open BPE

def formatProfile (profile : PreTokenizerProfile) : String :=
  match profile with
  | .cl100k => "cl100k"
  | .o200k => "o200k"

def parseIds (input : String) : Except String (List TokenId) := do
  let pieces := input.splitOn ","
  let rec go : List String → Except String (List TokenId)
    | [] => pure []
    | raw :: rest =>
        let piece := raw.trimAscii.toString
        if piece.isEmpty then go rest
        else
          match piece.toNat? with
          | some n => return n :: (← go rest)
          | none => throw s!"invalid token id '{piece}'"
  go pieces

def formatIds (ids : List TokenId) : String :=
  String.intercalate "," (ids.map toString)

def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  lean-bpe [--tokenizer <path>] info"
  IO.println "  lean-bpe [--tokenizer <path>] encode <text>"
  IO.println "  lean-bpe [--tokenizer <path>] decode <comma-separated token ids>"
  IO.println "  lean-bpe [--tokenizer <path>] roundtrip <text>"
  IO.println "  lean-bpe [--tokenizer <path>] check"
  IO.println "  lean-bpe [--tokenizer <path>] bench <newline-delimited dataset file>"
  IO.println "  lean-bpe [--tokenizer <path>] study <newline-delimited dataset file>"

def parseCliOptions : List String → Except String (Option System.FilePath × List String)
  | "--tokenizer" :: path :: rest => pure (some path, rest)
  | "--tokenizer" :: [] => throw "missing path after --tokenizer"
  | args => pure (none, args)

def loadTokenizerOrError
    (path : System.FilePath) :
    IO (Except String { tok : LoadedAsciiTokenizer // LoadedAsciiSound tok }) :=
  loadCertifiedAsciiTokenizer path

def main (args : List String) : IO UInt32 := do
  let parsed := parseCliOptions args
  match parsed with
  | .error err =>
      IO.eprintln err
      printUsage
      return 1
  | .ok (pathOpt, rest) =>
      match rest with
      | ["check"] =>
          runPackagedTests <|
            match pathOpt with
            | some path => [path]
            | none => supportedTokenizerPaths
      | ["bench", datasetPath] =>
          runSpeedBenchmark
            (match pathOpt with | some path => [path] | none => supportedTokenizerPaths)
            datasetPath
      | ["study", datasetPath] =>
          runEmpiricalStudy
            (match pathOpt with | some path => [path] | none => supportedTokenizerPaths)
            datasetPath
      | _ =>
          let path := pathOpt.getD defaultTokenizerPath
          let result ← loadTokenizerOrError path
          match result with
          | .error err =>
              IO.eprintln s!"failed to load tokenizer from {path}: {err}"
              pure 1
          | .ok ⟨tok, _⟩ =>
              match rest with
              | ["info"] =>
                  IO.println s!"path: {path}"
                  IO.println s!"profile: {formatProfile tok.profile}"
                  IO.println s!"merges: {tok.merges.size}"
                  IO.println s!"vocab: {tok.vocab.size}"
                  pure 0
              | ["encode", text] =>
                  match encodeExternalIds tok text with
                  | .ok ids =>
                      IO.println (formatIds ids)
                      pure 0
                  | .error err =>
                      IO.eprintln err
                      pure 1
              | ["decode", rawIds] =>
                  match parseIds rawIds with
                  | .ok ids =>
                      match decodeExternalIds tok ids with
                      | .ok text =>
                          IO.println text
                          pure 0
                      | .error err =>
                          IO.eprintln err
                          pure 1
                  | .error err =>
                      IO.eprintln err
                      pure 1
              | ["roundtrip", text] =>
                  match encodeExternalIds tok text with
                  | .ok ids =>
                      match decodeExternalIds tok ids with
                      | .ok decoded =>
                          IO.println s!"ids: {formatIds ids}"
                          IO.println s!"decoded: {decoded}"
                          pure 0
                      | .error err =>
                          IO.eprintln err
                          pure 1
                  | .error err =>
                      IO.eprintln err
                      pure 1
              | _ =>
                  printUsage
                  pure 1
