#!/usr/bin/env python3
"""rh-buildq publisher: upload modules Lake has finished in a build tree to the R2 cache.

usage: publish.py <queue-dir> [--once] [--interval SECONDS] [--settle SECONDS] [--before EPOCH]

<queue-dir> holds job.env (TARGET=<commit>), phase, project/ (the Lake workspace) and
known-maps/*.jsonl. The publisher exits after its first pass that starts once `phase` says
done or failed. --before skips archives modified after EPOCH (an interrupted build's last
seconds may have left partial files).

Each pass:
  * finds module traces (.lake/build/lib/lean/**/*.trace) whose input hash (trace "depHash")
    is not yet published and not already in the maps the build restored from;
  * requires the module's .lake/build/ir/<mod>.ltar to exist, be no older than the trace,
    and both to have been quiet for SETTLE seconds (Lake packs the ltar after writing the trace);
  * names the archive by stock Lake's content hash (computeBinFileHash, 16 hex), uploads it to
    artifacts/<repo>/<hash16>.art with If-None-Match:* (never overwrites);
  * then merges the new input-hash -> <hash16>.ltar entries into two Lake mapping files:
      rh-buildq/maps/<TARGET>.jsonl        everything this build published (delta over its restore)
      rh-buildq/pool/<toolchain-dir>.jsonl union of everything any rh-buildq publisher has published
    using compare-and-swap (If-Match ETag), so concurrent publishers cannot lose entries.
job.env options: MAP_PREFIX replaces the "rh-buildq" key prefix of both maps (tests); MAP_NAME
replaces <TARGET> in the per-build map key (rh-shard dispatch: one map per chunk, so two chunks of
one commit never share a per-build map).
Maps are stock Lake mapping files: `lake cache get --mappings-only <file>` (or `lake cache add`)
makes Lake fetch an artifact lazily whenever a module's input hash matches.
Credentials: $RH_BUILDQ_CREDS (default /etc/rh-buildq/r2.json), {"accessKeyId","secretAccessKey"}, 0600.
Lean: $RH_BUILDQ_LEAN, default `lean` of the project's toolchain under ~/.elan.
"""
import json, os, re, subprocess, sys, tempfile, time, hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

REPO = "leanprover-community/riemann-hypothesis"
ACCOUNT = "ec2169bdf033f56b009956d4b64ba8ef"
BUCKET = "riemann-hypothesis-cache"
S3 = f"https://{ACCOUNT}.r2.cloudflarestorage.com/{BUCKET}/"
PUBLIC = "https://rh-cache.taucetiproject.org/"
ART_TYPE = "application/vnd.reservoir.artifact"
MAP_TYPE = "application/vnd.reservoir.outputs+json-lines"
IMMUTABLE = "public, max-age=31536000, immutable"
SCHEMA = "2026-03-17"
CREDS = Path(os.environ.get("RH_BUILDQ_CREDS", "/etc/rh-buildq/r2.json"))
HASH = re.compile(r"[0-9a-f]{16}\Z")
SETTLE = 20
BATCH = 1500
WORKERS = 48
STATE_FILE = None
HASH_SOURCE = '''import Lake.Build.Trace
import Lean.Data.Json.FromToJson
open Lake Lean
def main (args : List String) : IO Unit := do
  let [jobs, output] := args | throw <| IO.userError "expected jobs and output"
  let input ← IO.FS.Handle.mk jobs .read
  let out ← IO.FS.Handle.mk output .write
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok job := Json.parse line | throw <| IO.userError "invalid job"
    let .ok file := job.getObjValAs? String "file" | throw <| IO.userError "missing file"
    let actual := (← computeBinFileHash file).toString
    out.putStrLn (Json.mkObj [("file", toJson file), ("actual", toJson actual)]).compress
'''


def log(msg):
    print(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), msg, flush=True)


def read_env(path):
    env = {}
    for line in Path(path).read_text().splitlines():
        if "=" in line and not line.startswith("#"):
            k, v = line.split("=", 1)
            env[k] = v.strip().strip('"')
    return env


class R2:
    def __init__(self, temp):
        c = json.loads(CREDS.read_text())
        self.conf = Path(temp) / "curl-auth.conf"
        fd = os.open(self.conf, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w") as f:  # keeps the secret out of argv
            f.write(f'user = "{c["accessKeyId"]}:{c["secretAccessKey"]}"\naws-sigv4 = "aws:amz:auto:s3"\n')

    def _curl(self, args, body=None):
        hdr = tempfile.NamedTemporaryFile(delete=False)
        hdr.close()
        cmd = ["curl", "-sS", "-K", str(self.conf), "-D", hdr.name, "-o", "-", "-w", "\n%{http_code}",
               "--retry", "3", "--retry-all-errors", "--max-time", "300", *args]
        r = subprocess.run(cmd, input=body, capture_output=True)
        headers = Path(hdr.name).read_text(errors="replace"); os.unlink(hdr.name)
        out = r.stdout
        data, _, code = out.rpartition(b"\n")
        etag = None
        for line in headers.splitlines():
            if line.lower().startswith("etag:"):
                etag = line.split(":", 1)[1].strip()
        return int(code or 0), data, etag

    def get(self, key):
        code, data, etag = self._curl([S3 + key])
        if code == 404:
            return None, None
        if code != 200:
            raise RuntimeError(f"GET {key}: HTTP {code}")
        return data, etag

    def put(self, key, *, file=None, data=None, ctype, cache, etag=None, meta=None):
        args = ["-X", "PUT", "-H", "Content-Type: " + ctype, "-H", "Cache-Control: " + cache,
                "-H", ("If-Match: " + etag) if etag else "If-None-Match: *"]
        for k, v in (meta or {}).items():
            args += ["-H", f"x-amz-meta-{k}: {v}"]
        if file:
            args += ["--data-binary", "@" + str(file)]
            body = None
        else:
            args += ["--data-binary", "@-"]
            body = data
        code, out, _ = self._curl(args + [S3 + key], body)
        if code in (200, 201):
            return True
        if code == 412:
            return False
        raise RuntimeError(f"PUT {key}: HTTP {code} {out[:200]!r}")


def parse_map(data):
    lines = data.decode().splitlines()
    if not lines or json.loads(lines[0]) != SCHEMA:
        raise ValueError("unexpected map schema")
    return {k: v for k, v in (json.loads(l) for l in lines[1:] if l)}


def encode_map(m):
    return (json.dumps(SCHEMA) + "\n" + "".join(json.dumps([k, v], separators=(",", ":")) + "\n"
                                                 for k, v in sorted(m.items()))).encode()


def merge_remote(r2, key, new):
    """CAS-merge `new` into the map at `key`; never drops entries; keeps existing values on conflict."""
    for _ in range(20):
        data, etag = r2.get(key)
        cur = parse_map(data) if data else {}
        merged = dict(new); merged.update(cur)
        if data and len(merged) == len(cur):
            return len(cur)
        if r2.put(key, data=encode_map(merged), ctype=MAP_TYPE, cache="no-cache", etag=etag):
            return len(merged)
        time.sleep(1)
    raise RuntimeError(f"map CAS did not settle: {key}")


SPOT = None  # None: not probed yet; False: no EC2 metadata service here


def spot_notice():
    """True once EC2 has scheduled a Spot interruption (IMDSv2 spot/instance-action)."""
    global SPOT
    if SPOT is False:
        return False
    try:
        tok = subprocess.run(["curl", "-sf", "-m", "2", "-X", "PUT", "http://169.254.169.254/latest/api/token",
                              "-H", "X-aws-ec2-metadata-token-ttl-seconds: 300"], capture_output=True, text=True).stdout
        if SPOT is None:
            SPOT = bool(tok)
            if not tok:
                return False
        r = subprocess.run(["curl", "-sf", "-m", "2", "-H", "X-aws-ec2-metadata-token: " + tok,
                            "http://169.254.169.254/latest/meta-data/spot/instance-action"], capture_output=True)
        return r.returncode == 0 and bool(r.stdout)
    except OSError:
        return False


def lake_hashes(lean, paths, work):
    src, jobs, out = work / "Hash.lean", work / "hash-jobs.jsonl", work / "hashes.jsonl"
    src.write_text(HASH_SOURCE)
    jobs.write_text("".join(json.dumps({"file": str(p)}) + "\n" for p in paths))
    lib = lean.parent.parent / "lib/lean/libLake_shared.so"
    subprocess.run([str(lean), f"--load-dynlib={lib}", "--run", str(src), str(jobs), str(out)], cwd=work, check=True)
    return {row["file"]: row["actual"] for row in map(json.loads, out.read_text().splitlines())}


def save_state(state):
    state["errors"] = state["errors"][-20:]
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps({k: v for k, v in state.items() if k != "_seen"}))
    os.chmod(tmp, 0o644); os.replace(tmp, STATE_FILE)


def known_hashes(Q, env):
    """Input hashes already available remotely (what the build restored from); skip re-uploading."""
    known = set()
    for f in sorted((Q / "known-maps").glob("*.jsonl")):
        try:
            known.update(parse_map(f.read_bytes()))
        except Exception as e:
            log(f"warn: cannot read {f}: {e}")
    return known


def one_pass(Q, env, r2, state, known, lean, work, before=None):
    P = Q / "project"
    lib, ir = P / ".lake/build/lib/lean", P / ".lake/build/ir"
    published = state["published"]
    now = time.time()
    cands = []
    if not lib.is_dir():
        return 0
    seen = state.setdefault("_seen", {})  # trace path -> mtime already decided (in memory only)
    for trace in lib.rglob("*.trace"):
        rel = trace.relative_to(lib).with_suffix("")
        try:
            tst = trace.stat()
            if seen.get(str(trace)) == tst.st_mtime:
                continue
            if now - tst.st_mtime < SETTLE:
                continue
            dep = json.loads(trace.read_text()).get("depHash")
        except (OSError, ValueError):
            continue
        if not isinstance(dep, str) or not HASH.fullmatch(dep) or dep in published or dep in known:
            seen[str(trace)] = tst.st_mtime
            continue
        ltar = ir / (str(rel) + ".ltar")
        try:
            lst = ltar.stat()
        except OSError:
            continue
        if lst.st_mtime + 1 < tst.st_mtime or now - lst.st_mtime < SETTLE:
            continue  # stale (pre-rebuild) or still being written
        if before is not None and max(lst.st_mtime, tst.st_mtime) > before:
            continue  # written in the last moments of an interrupted build
        cands.append((str(rel).replace("/", "."), dep, ltar))
    if not cands:
        return 0
    total_new = 0
    for i in range(0, len(cands), BATCH):
        total_new += publish_batch(cands[i:i + BATCH], env, r2, state, lean, work, lib)
    log(f"pass: candidates={len(cands)} published+={total_new} total={len(published)} "
        f"uploaded={state['uploaded']} present={state['already_present']} seconds={time.time() - now:.0f}")
    return total_new


def publish_batch(cands, env, r2, state, lean, work, lib):
    """Hash, upload in parallel, then CAS-merge the maps once for the whole batch."""
    published = state["published"]
    hashes = lake_hashes(lean, [c[2] for c in cands], work)
    def upload(item):
        name, dep, ltar = item
        h = hashes.get(str(ltar))
        if not h or not HASH.fullmatch(h):
            raise RuntimeError("no Lake hash")
        # Re-check that the trace did not change while hashing.
        if json.loads((lib / (name.replace(".", "/") + ".trace")).read_text()).get("depHash") != dep:
            return None
        sha = hashlib.sha256(ltar.read_bytes()).hexdigest()
        created = r2.put(f"artifacts/{REPO}/{h}.art", file=ltar, ctype=ART_TYPE, cache=IMMUTABLE, meta={"sha256": sha})
        return dep, h + ".ltar", created
    new, errors = {}, 0
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        futures = {pool.submit(upload, c): c for c in cands}
        for f in as_completed(futures):
            try:
                r = f.result()
            except Exception as e:
                errors += 1
                state["errors"].append(f"{time.strftime('%H:%M:%S')} {futures[f][0]}: {e}"[:300])
                continue
            if r:
                new[r[0]] = r[1]
                state["uploaded" if r[2] else "already_present"] += 1
    if new:
        tc = env["TOOLCHAIN_DIR"]
        prefix = env.get("MAP_PREFIX") or "rh-buildq"
        merge_remote(r2, f"{prefix}/maps/{env.get('MAP_NAME') or env['TARGET']}.jsonl", {**published, **new})
        state["pool_size"] = merge_remote(r2, f"{prefix}/pool/{tc}.jsonl", new)
        published.update(new)
        save_state(state)
    if errors:
        log(f"batch: {errors} upload errors")
    return len(new)




def main():
    global SETTLE
    Q = Path(sys.argv[1]).resolve()
    once = "--once" in sys.argv
    interval = int(sys.argv[sys.argv.index("--interval") + 1]) if "--interval" in sys.argv else 60
    if "--settle" in sys.argv:
        SETTLE = int(sys.argv[sys.argv.index("--settle") + 1])
    before = float(sys.argv[sys.argv.index("--before") + 1]) if "--before" in sys.argv else None
    env = read_env(Q / "job.env")
    if "TOOLCHAIN_DIR" not in env:
        tc = (Q / "project/lean-toolchain").read_text().strip()
        env["TOOLCHAIN_DIR"] = tc.replace("/", "--").replace(":", "---")
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    lean = Path(os.environ.get("RH_BUILDQ_LEAN", elan / "toolchains" / env["TOOLCHAIN_DIR"] / "bin/lean"))
    global STATE_FILE
    sf = STATE_FILE = Q / "publish-state.json"
    state = json.loads(sf.read_text()) if sf.exists() else {}
    state.setdefault("published", {}); state.setdefault("uploaded", 0); state.setdefault("already_present", 0)
    state.setdefault("errors", []); state.setdefault("pool_size", 0)
    with tempfile.TemporaryDirectory(prefix="rh-buildq-pub-") as temp:
        work = Path(temp)
        r2 = R2(temp)
        known = known_hashes(Q, env)
        log(f"publisher start target={env['TARGET']} known={len(known)} already_published={len(state['published'])}")
        while True:
            start = time.time()
            try:
                one_pass(Q, env, r2, state, known, lean, work, before)
            except Exception as e:
                state["errors"] = (state["errors"] + [f"{time.strftime('%H:%M:%S')} pass: {e}"[:300]])[-20:]
                log(f"pass failed: {e}")
            state["last_pass"] = int(time.time())
            save_state(state)
            phase = (Q / "phase").read_text().strip() if (Q / "phase").exists() else ""
            if once:
                return
            if phase in ("done", "failed") and start > (Q / "phase").stat().st_mtime + SETTLE + 5:
                log(f"build {phase}; final pass complete")
                return
            # Sleep in slices; on a Spot interruption notice (~2 min warning) publish back to back
            # with a short quiet period so as little as possible is lost.
            deadline = start + interval
            while time.time() < deadline:
                if spot_notice():
                    if SETTLE != 3:
                        log("spot interruption notice: publishing continuously")
                    SETTLE = 3
                    break
                time.sleep(5)


if __name__ == "__main__":
    main()
