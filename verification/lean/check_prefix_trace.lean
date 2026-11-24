import Logkeeper.PrefixTrace

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "expected one trace path")
  let lines ← IO.FS.lines path
  match Logkeeper.PrefixTrace.validate lines.toList with
  | .ok count =>
    IO.println s!"accepted {count} events"
    return 0
  | .error reason =>
    IO.eprintln reason
    return 1
