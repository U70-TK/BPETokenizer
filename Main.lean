import LeanBPETokenizer

open BPE

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
  IO.println "  lean-bpe encode <text>"
  IO.println "  lean-bpe decode <comma-separated token ids>"
  IO.println "  lean-bpe roundtrip <text>"

def main (args : List String) : IO UInt32 := do
  let result ← loadAsciiTokenizer
  match result with
  | .error err =>
      IO.eprintln s!"failed to load tokenizer: {err}"
      return 1
  | .ok tok =>
      match args with
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
