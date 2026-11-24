import Logkeeper.StreamTrace

open Logkeeper.StreamTrace

def checkTrace (path : System.FilePath) (requireReference : Bool) : IO UInt32 := do
  let file ← IO.FS.Handle.mk path .read
  let mut seed := none
  let mut seeds := 0
  let mut events := 0
  let mut publications := 0
  let mut incompleteSyncs := 0
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
      let some current := seed | throw (IO.userError s!"line {line}: missing seed")
      match parse row with
      | .error message =>
          IO.eprintln s!"line {line}: {message}"
          return 1
      | .ok (serial, keeper, projection) =>
          events := events + 1
          match projection with
          | .checked => pure ()
          | .inheritedPublication =>
              if requireReference then
                IO.eprintln s!"line {line}: Study 119 inherited publication"
                return 1
              if publications == 0 then
                IO.println s!"inherited publication witness: seed {current}, RPC {serial}, keeper {keeper}, line {line}"
              publications := publications + 1
          | .incompleteSync =>
              if requireReference then
                IO.eprintln s!"line {line}: Study 119 incomplete Sync tail"
                return 1
              if incompleteSyncs == 0 then
                IO.println s!"incomplete Sync witness: seed {current}, RPC {serial}, keeper {keeper}, line {line}"
              incompleteSyncs := incompleteSyncs + 1
  IO.println s!"{seeds} seeds, {events} effects, {publications} inherited publications, {incompleteSyncs} changed incomplete Sync tails"
  return 0

def main : List String → IO UInt32
  | [path] => checkTrace path false
  | ["--require-reference", path] => checkTrace path true
  | _ => do
      IO.eprintln "usage: check_stream_trace.lean [--require-reference] STREAM_TRACE"
      return 2
