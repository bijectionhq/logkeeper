import Logkeeper.StreamTrace

open Logkeeper.StreamTrace

def checkTrace (path : System.FilePath) : IO UInt32 := do
  let file ← IO.FS.Handle.mk path .read
  let mut seed := none
  let mut seeds := 0
  let mut events := 0
  let mut counts : List (Projection × Nat) := Projection.all.map (·, 0)
  let mut line := 0
  repeat
    let row ← file.getLine
    if row.isEmpty then break
    line := line + 1
    let row := row.trimAsciiEnd.toString
    if let ["seed", token] := row.splitOn " " then
      let some index := token.toNat? | throw (IO.userError s!"line {line}: invalid seed")
      if let some previous := seed then
        unless index == previous + 1 do throw (IO.userError s!"line {line}: nonconsecutive seed")
      seed := some index
      seeds := seeds + 1
    else
      if seed.isNone then throw (IO.userError s!"line {line}: missing seed")
      match parse row >>= step with
      | .error message =>
          IO.eprintln s!"line {line}: {message}"
          return 1
      | .ok projection =>
          events := events + 1
          counts := counts.map fun (kind, count) => (kind, if kind == projection then count + 1 else count)
  let summary := ", ".intercalate (counts.map fun (kind, count) => s!"{count} {kind.name}")
  IO.println s!"{seeds} seeds, {events} effects: {summary}"
  return 0

def main : List String → IO UInt32
  | [path] => checkTrace path
  | _ => do
      IO.eprintln "usage: check_stream_trace.lean STREAM_TRACE"
      return 2
