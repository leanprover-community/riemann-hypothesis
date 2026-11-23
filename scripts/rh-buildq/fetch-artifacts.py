#!/usr/bin/env python3
"""Download every artifact named in a Lake map that is missing from a local Lake cache.

usage: fetch-artifacts.py <map.jsonl> <cache-dir> [--sha256 <file>]
Stock Lake 4.37 does not download artifacts lazily during `lake build`: a mapped module whose
artifact is absent locally is simply compiled. So restores must prefetch. One curl process
downloads up to 500 files at a time (fd soft limit raised to match) and retries transport
errors and CDN 5xx. Files land in <cache-dir>/artifacts/<hash16>.ltar atomically, so a file
there is always complete. Objects are content-addressed and write-once (If-None-Match) in R2.
--sha256 names a JSON object {"<hash16>.ltar": "<sha256>"} (e.g. from a CI module manifest):
those downloads are verified before they are moved into the cache, and a mismatch is discarded
and downloaded again. Up to three passes; exit 1 if anything is still missing.
Requires curl 7.83 or newer to remove incomplete outputs after transfer errors.
"""
import hashlib, json, os, resource, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PUBLIC = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/"
PARALLEL = 500


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def main():
    args = sys.argv[1:]
    digests = {}
    if "--sha256" in args:
        i = args.index("--sha256")
        digests = json.loads(Path(args[i + 1]).read_text())
        del args[i:i + 2]
    mapping, cache = Path(args[0]), Path(args[1]) / "artifacts"
    cache.mkdir(parents=True, exist_ok=True)
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    want = 65536 if hard == resource.RLIM_INFINITY else min(hard, 65536)
    if soft != resource.RLIM_INFINITY and soft < want:
        resource.setrlimit(resource.RLIMIT_NOFILE, (want, hard))
    lines = mapping.read_text().splitlines()[1:]
    names = sorted({json.loads(l)[1] for l in lines if l})
    missing = [n for n in names if not (cache / n).exists()]
    print(f"fetch-artifacts: {len(names)} mapped, {len(missing)} missing locally", flush=True)
    for attempt in range(1, 4):
        if not missing:
            break
        with tempfile.TemporaryDirectory(prefix="fetch-", dir=cache.parent) as t:
            conf = Path(t) / "curl.conf"
            conf.write_text("".join(f'url = "{PUBLIC}{n[:-5]}.art"\noutput = "{t}/{n}"\n' for n in missing))
            r = subprocess.run(["curl", "--disable", "--fail", "--remove-on-error", "--silent", "--show-error", "--location",
                                "--user-agent", "rh-buildq/1", "--retry", "5", "--retry-all-errors",
                                "--connect-timeout", "30", "--max-time", "600",
                                "--parallel", "--parallel-max", str(PARALLEL), "--config", str(conf)])

            def settle(n):
                p = Path(t) / n
                if not (p.is_file() and p.stat().st_size):
                    return "missing"
                if n in digests and sha256(p) != digests[n]:
                    p.unlink()
                    return "corrupt"
                os.chmod(p, 0o444)
                os.replace(p, cache / n)
                return "ok"

            with ThreadPoolExecutor(32) as pool:
                results = list(pool.map(settle, missing))
        corrupt = [n for n, s in zip(missing, results) if s == "corrupt"]
        missing = [n for n, s in zip(missing, results) if s != "ok"]
        print(f"fetch-artifacts: pass {attempt}: downloaded {len(results) - len(missing)}/{len(results)}"
              f" (curl exit {r.returncode}; {len(corrupt)} failed SHA-256 verification)", flush=True)
        for n in corrupt[:10]:
            print(f"fetch-artifacts: SHA-256 mismatch for {n}", flush=True)
    sys.exit(1 if missing else 0)


if __name__ == "__main__":
    main()
