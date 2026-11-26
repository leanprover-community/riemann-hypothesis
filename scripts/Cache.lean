import Init.System.IO

/-- Fetch Mathlib and the project's published artifacts using stock tools. -/
def main (args : List String) : IO UInt32 := do
  if args != ["get"] then
    IO.eprintln "Usage: lake exe cache get"
    return 2
  let candidates := if System.Platform.isWindows then
    #[("py", #["-3"]), ("python", #[]), ("python3", #[])]
  else
    #[("python3", #[]), ("python", #[])]
  for (cmd, launcherArgs) in candidates do
    let supported ← try
      let probe ← IO.Process.output {
        cmd
        args := launcherArgs ++ #["-I", "-c", "import sys; sys.exit(sys.version_info < (3, 11))"]
      }
      pure (probe.exitCode == 0)
    catch _ => pure false
    if supported then
      let child ← IO.Process.spawn {
        cmd
        args := launcherArgs ++ #["-I", "scripts/lake-cache-get.py"]
      }
      return ← child.wait
  IO.eprintln "lake exe cache get needs Python 3.11 or newer on PATH"
  return 1
