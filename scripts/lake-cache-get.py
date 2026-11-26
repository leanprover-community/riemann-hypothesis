"""Fetch Mathlib, Tau Ceti and this project's build cache in order."""

import os
from pathlib import Path
import runpy
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    # Load the sibling by path so this also works in Python's isolated mode.
    downloader = runpy.run_path(str(ROOT / "scripts" / "fetch-artifacts.py"))
    downloader["raise_open_file_limit"]()

    env = os.environ.copy()
    env["MATHLIB_CACHE_GET_URL"] = env.get("MATHLIB_CACHE_GET_URL") or "https://cache.mathlib.org/mathlib4"
    print("Fetching Mathlib cache...", flush=True)
    code = subprocess.run(["lake", "exe", "mathlib/cache", "get"], cwd=ROOT, env=env).returncode
    if code:
        return code

    env["LAKE_CACHE_DIR"] = str(ROOT / ".lake" / "cache")
    print("Fetching Tau Ceti cache...", flush=True)
    code = subprocess.run([sys.executable, "-I", "scripts/tauceti-cache-get.py"],
                          cwd=ROOT, env=env).returncode
    if code:
        return code

    code = subprocess.run([sys.executable, "-I", "scripts/ci-cache-get.py"],
                          cwd=ROOT, env=env).returncode
    if code == 3:
        print("No validated cache matches these build inputs; use lake build.", file=sys.stderr)
    return code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except OSError as error:
        sys.exit(f"lake exe cache get: {error}")
