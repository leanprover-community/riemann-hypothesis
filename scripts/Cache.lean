import Init.System.IO

/-- Whether `path` is one of the `bash.exe` launchers that Windows ships for WSL. -/
def isWslLauncher (path : System.FilePath) : Bool :=
  let p := path.toString.toLower.replace "/" "\\"
  (p.splitOn "\\windows\\system32\\").length > 1 || (p.splitOn "\\windowsapps\\").length > 1

/-- The bash that runs `scripts/lake-cache-get.sh`. Elsewhere it is plain `bash`. On Windows,
process creation searches `System32` before `PATH`, so plain `bash` starts WSL, which sees
neither Lake nor Windows' Python. Use `RH_CACHE_BASH` if it is set, else the first `bash.exe` on
`PATH` that is not a WSL launcher, else `bin/bash.exe` of the Git for Windows that runs `git`. -/
def findBash : IO String := do
  unless System.Platform.isWindows do
    return "bash"
  if let some bash ← IO.getEnv "RH_CACHE_BASH" then
    return bash
  for dir in System.SearchPath.parse ((← IO.getEnv "PATH").getD "") do
    unless dir.isAbsolute do continue  -- an empty or relative entry would resolve against the cwd
    let bash := dir / "bash.exe"
    if !isWslLauncher bash && (← bash.pathExists) then
      return bash.toString
  -- `git --exec-path` is `<Git root>/mingw64/libexec/git-core` (or `clangarm64/...`).
  let exec ← try
      some <$> IO.Process.output { cmd := "git", args := #["--exec-path"] }
    catch _ => pure none
  if let some out := exec then
    if out.exitCode == 0 then
      let core : System.FilePath := out.stdout.trimAscii.toString
      if let some root := core.parent >>= (·.parent) >>= (·.parent) then
        let bash := root / "bin" / "bash.exe"
        if ← bash.pathExists then
          return bash.toString
  throw <| IO.userError
    "lake exe cache get needs Git for Windows' bash; set RH_CACHE_BASH to the path of its bash.exe"

/-- Fetch Mathlib and the project's published artifacts using stock tools. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := ← findBash
    args := #["scripts/lake-cache-get.sh"] ++ args.toArray
  }
  child.wait
