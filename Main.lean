import Rfc4648

/-- The base encodings this REPL can apply. -/
inductive Encoding
  | base16
  | base32
  | base64

namespace Encoding

def encode : Encoding → ByteArray → String
  | .base16 => Rfc4648.Base16.encode
  | .base32 => Rfc4648.Base32.encode
  | .base64 => Rfc4648.Base64.encode

def decode? : Encoding → String → Option ByteArray
  | .base16 => Rfc4648.Base16.decode?
  | .base32 => Rfc4648.Base32.decode?
  | .base64 => Rfc4648.Base64.decode?

def name : Encoding → String
  | .base16 => "Base16"
  | .base32 => "Base32"
  | .base64 => "Base64"

/-- Parse the user's choice of encoding from a menu selection. -/
def ofChoice? (s : String) : Option Encoding :=
  match s.trimAscii.toString.toLower with
  | "1" | "64" | "base64" | "" => some .base64
  | "2" | "32" | "base32" => some .base32
  | "3" | "16" | "base16" | "hex" => some .base16
  | _ => none

end Encoding

/-- Whether the REPL encodes text into a base, or decodes a base back to bytes. -/
inductive Mode
  | encode
  | decode

namespace Mode

def name : Mode → String
  | .encode => "encode"
  | .decode => "decode"

/-- Parse the user's choice of direction from a menu selection. -/
def ofChoice? (s : String) : Option Mode :=
  match s.trimAscii.toString.toLower with
  | "1" | "e" | "enc" | "encode" | "" => some .encode
  | "2" | "d" | "dec" | "decode" => some .decode
  | _ => none

end Mode

/-- Render decoded bytes: as text when valid UTF-8, otherwise as a byte listing. -/
def renderBytes (bytes : ByteArray) : String :=
  match String.fromUTF8? bytes with
  | some s => s
  | none => "<" ++ String.intercalate " " (bytes.toList.map (fun b => toString b.toNat)) ++ ">"

/-- Read lines from stdin, applying `mode`/`enc` to each until EOF. -/
partial def loop (stdin : IO.FS.Stream) (mode : Mode) (enc : Encoding) : IO Unit := do
  let line ← stdin.getLine
  -- An empty read (no trailing newline) signals EOF.
  if line.isEmpty then
    IO.println "Goodbye!"
    return
  -- getLine keeps the trailing newline; drop it before processing.
  let text := (line.dropEndWhile (fun c => c == '\n' || c == '\r')).toString
  match mode with
  | .encode => IO.println (enc.encode text.toUTF8)
  | .decode =>
    match enc.decode? text with
    | some bytes => IO.println (renderBytes bytes)
    | none => IO.eprintln s!"Not valid {enc.name}: {text}"
  loop stdin mode enc

def main : IO Unit := do
  let stdin ← IO.getStdin
  IO.println "Encode or decode? [1] encode (default)  [2] decode"
  IO.print "> "
  let modeChoice ← stdin.getLine
  match Mode.ofChoice? modeChoice with
  | none =>
    IO.eprintln s!"Unrecognized mode: {modeChoice.trimAscii}"
  | some mode =>
    IO.println "Which encoding? [1] Base64 (default)  [2] Base32  [3] Base16"
    IO.print "> "
    let encChoice ← stdin.getLine
    match Encoding.ofChoice? encChoice with
    | none =>
      IO.eprintln s!"Unrecognized encoding: {encChoice.trimAscii}"
    | some enc =>
      IO.println s!"Ready to {mode.name} {enc.name}. Type a line; Ctrl-D to quit."
      loop stdin mode enc
