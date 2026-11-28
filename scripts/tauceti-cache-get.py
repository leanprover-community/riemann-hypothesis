#!/usr/bin/env python3
"""Fetch the oleans of the Tau Ceti modules that this project imports.

Tau Ceti (https://github.com/TauCetiProject/TauCeti) publishes its build outputs in its own
public Lake artifact cache, the service `tauceti-public` of `lakefile.toml`. Neither Mathlib's
cache tool nor this project's cache covers it. This script, run by `lake exe cache get` after
Mathlib's cache and before the project's, does four things:

0. checks that `src/Statements.lean`, `src/Main.lean` and `Challenge.lean` import no Tau Ceti
   module, so that the five statements keep depending on Mathlib alone;
1. checks that the Tau Ceti revision pinned in `lake-manifest.json` was built against the Mathlib
   commit pinned there, since otherwise none of Tau Ceti's cached oleans match and Lake would
   compile every imported Tau Ceti module from source;
2. downloads Tau Ceti's input-to-output mappings for the pinned revision
   (`lake cache get --mappings-only`; about 135 MB the first time);
3. runs `lake build` on the Tau Ceti modules that `src` needs: those imported anywhere under
   `src`, together with every Tau Ceti module they import in turn, publicly or not. Lake restores
   a cached module without the modules it imports only privately, but a later
   `lake build --no-build` checks those too, so they are fetched explicitly. This downloads and
   unpacks exactly the oleans needed, without compiling.

It only reads from Tau Ceti's cache; it never uploads. It verifies nothing about proofs.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
CACHE_IMPORTS = ROOT / "scripts" / "CacheImports.lean"


def say(message):
    print(f"[Tau Ceti cache] {message}", flush=True)


def package(manifest, name):
    for entry in manifest["packages"]:
        if entry["name"] == name:
            return entry
    raise ValueError(f"{name} is not in {manifest.get('name', 'the')} manifest")


def check_mathlib_pin():
    ours = json.loads((ROOT / "lake-manifest.json").read_text())
    tauceti = package(ours, "TauCeti")
    theirs_path = ROOT / ".lake" / "packages" / "TauCeti" / "lake-manifest.json"
    if not theirs_path.is_file():
        raise ValueError(f"{theirs_path} is missing; run `lake update TauCeti` or `lake build` first")
    theirs = json.loads(theirs_path.read_text())
    ours_mathlib, theirs_mathlib = package(ours, "mathlib")["rev"], package(theirs, "mathlib")["rev"]
    if ours_mathlib != theirs_mathlib:
        raise ValueError(
            f"Tau Ceti {tauceti['inputRev']} ({tauceti['rev'][:12]}) was built against Mathlib "
            f"{theirs_mathlib[:12]}, but this project pins Mathlib {ours_mathlib[:12]}. Its cached "
            "oleans cannot be used; move the two pins together (see CACHE.md).")
    say(f"Tau Ceti {tauceti['inputRev']} ({tauceti['rev'][:12]}) uses this project's Mathlib "
        f"{ours_mathlib[:12]}")


TRUSTED_FILES = ("src/Statements.lean", "src/Main.lean", "Challenge.lean")


def import_headers(root=ROOT):
    """Parse source headers, `Challenge.lean`, and reachable Tau Ceti headers with Lean."""
    result = subprocess.run(["lean", "--run", str(CACHE_IMPORTS), str(root)], cwd=ROOT,
                            check=True, capture_output=True, text=True, encoding="utf-8")
    rows = json.loads(result.stdout)
    imports = {}
    root_resolved = root.resolve()
    for row in rows:
        if row["error"] is not None:
            raise ValueError(f"could not parse Lean imports in {row['path']}: {row['error']}")
        path = Path(row["path"]).resolve()
        imports[path.relative_to(root_resolved).as_posix()] = row["imports"]
    return imports


def check_trusted_files(imports):
    for name in TRUSTED_FILES:
        if name not in imports:
            raise ValueError(f"{name} is missing")
        if imports[name]:
            raise ValueError(f"{name} imports a Tau Ceti module: {', '.join(imports[name])}")


def imported_modules(imports, root=ROOT):
    """The Tau Ceti modules imported under `src`, closed under Tau Ceti's own imports (public,
    private and `meta` alike)."""
    pending = {
        module
        for path, modules in imports.items()
        if path.startswith("src/")
        for module in modules
    }
    direct = len(pending)
    source = root / ".lake" / "packages" / "TauCeti"
    modules = set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        modules.add(module)
        rel = Path(".lake", "packages", "TauCeti", *module.split(".")).with_suffix(".lean").as_posix()
        if rel not in imports:
            path = source.joinpath(*module.split(".")).with_suffix(".lean")
            raise ValueError(f"{module} is imported but {path} is missing")
        pending |= set(imports[rel]) - modules
    say(f"{direct} Tau Ceti module(s) imported under src, {len(modules)} with their imports")
    return sorted(modules)


def run_lake(args, env):
    return subprocess.run(["lake", *args], cwd=ROOT, env=env).returncode


def main():
    imports = import_headers()
    check_trusted_files(imports)
    check_mathlib_pin()
    env = os.environ.copy()
    for key in list(env):
        # Read-only use of a public cache: never pass upload credentials to Lake.
        if key.startswith(("AWS_", "CLOUDFLARE_", "CF_")) or key in (
                "LAKE_CACHE_KEY", "LAKE_CACHE_ARTIFACT_ENDPOINT", "LAKE_CACHE_REVISION_ENDPOINT",
                "LAKE_CACHE_SERVICE", "LAKE_ARTIFACT_CACHE"):
            env.pop(key)
    env["LAKE_CONFIG"] = str(ROOT / "lakefile.toml")
    say("fetching Tau Ceti's cache mappings")
    code = run_lake(["cache", "get", "--package", "TauCeti", "--service", "tauceti-public",
                     "--repo", "TauCetiProject/TauCeti", "--mappings-only"], env)
    if code:
        say("fetching the mappings failed; Lake would compile Tau Ceti modules from source")
        return code
    modules = imported_modules(imports)
    if not modules:
        say("no Tau Ceti module is imported under src; nothing more to fetch")
        return 0
    say(f"fetching oleans for those {len(modules)} Tau Ceti module(s)")
    code = run_lake(["-q", "build", *modules], env)
    if code:
        say("fetching Tau Ceti oleans failed")
    return code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError) as error:
        sys.exit(f"[Tau Ceti cache] stopped: {error}")
