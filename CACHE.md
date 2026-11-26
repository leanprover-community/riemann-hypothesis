# Build cache

This branch is the readable edition (`grh/`) of https://github.com/lsernau/grh-lean commit
72fead102f663d5c7a407964a13dc0cf9d977207, moved to the repository root, plus configuration and
scripts for a shared build cache. No file under `src`, and no `Challenge.lean`, `comparator.json`,
`lake-manifest.json` or `lean-toolchain`, is changed. The additions are `CACHE.md`, a note at the
top of `README.md`, the marked lines in `lakefile.toml`, `Cache.lean`, `lake-cache-get.sh`,
`ci-cache-get.py`, `ci-cache-stage.py`, `publish-ci-cache.py`, `ci-github.py`,
`fetch-artifacts.py`, `tauceti-cache-get.py`, `cache-baseline.json`, `runner/` and `tests/` in
`scripts`, and the workflows `.github/workflows/build.yml` and
`.github/workflows/publish-ci-cache.yml`. The Tau Ceti dependency (below) adds one entry to
`lake-manifest.json`. The scripts are copied or adapted from
`scripts/` of the earlier `main` branch of https://github.com/leanprover-community/riemann-hypothesis
(now the branch `alpoge`).

**The cached files were built from an unverified third-party proof, and the cache does not verify
anything.** The checks in the scripts only establish that you have the bytes which were published
for your exact build inputs. To check the proof, build it from source yourself, without this cache.

## Use

    lake exe cache get
    lake build

This needs Python 3.11 or newer and curl 7.71 or newer, and no credential. It fetches Mathlib's
cache, then Tau Ceti's, then this project's, and unpacks them. It ends with `lake build --no-build`, which must report
that nothing needs compiling. `lake exe mathlib/cache get` fetches Mathlib alone.

A change to the sources, `lakefile.toml`, `lake-manifest.json` or `lean-toolchain` gives different
build inputs; `lake exe cache get` then says that no cache matches.

## Baseline

When no record matches, `python3 scripts/ci-cache-get.py --baseline origin/main` (after
`lake exe cache get` has fetched Mathlib) restores a baseline instead: the record of the nearest
commit on `origin/main`'s first-parent history (up to 200 commits) that has one, else the record
pinned in `scripts/cache-baseline.json`. Each candidate is looked up by its own input
fingerprint, computed from Git objects with the same code as for the current inputs, and only
candidates with the current `lean-toolchain` and `lake-manifest.json` are tried. The baseline's
map, module manifest and artifacts get the same SHA-256 checks as an exact match. `lake build`
then compiles only the modules whose inputs differ from the baseline's, and the modules whose
imports changed as a result; it reuses the rest. The script exits 4 when it has restored a
baseline. `python3 -I scripts/tests/test_ci_cache_baseline.py` tests the selection.

## CI

Pull requests land through GitHub's merge queue. `.github/workflows/build.yml` has one job,
`lake build`, the queue's required check. It builds every pull request to `main` on a
GitHub-hosted runner, and every merge queue group (`merge_group`), push to `main` and manual run
on the self-hosted runner described below, with the exact record if there is one and the
baseline otherwise. It fails if `lake build` fails, if the build log has Lean's warning that a
declaration uses `sorry`, or if `scripts/PrintAxioms.lean` reports any axiom other than `propext`,
`Classical.choice` and `Quot.sound` for the five theorems. It never publishes anything.

On the self-hosted runner the job builds with `lake build -o`, then `scripts/ci-cache-stage.py`
writes the map, the module manifest and the artifacts that the public cache does not have yet,
and the job uploads them as the Actions artifact `cache-<commit>`. The push build of a commit
that the merge queue has already built stops after checking that (`scripts/ci-github.py
queue-tested`).

`.github/workflows/publish-ci-cache.yml` publishes them. On each push to `main` it finds the
build of that commit (the `merge_group` run, since the queue moves `main` to the exact commit it
built; else the push build of the commit, once it has finished), and checks its artifact with the
code of `main` on a fresh GitHub-hosted runner, running nothing from the artifact or the commit:
the record is computed from the commit's Git objects, the map and manifest must pass
`ci-cache-get.py`'s checks for those inputs, the modules must be exactly the source files under
`src`, and every artifact (staged, or else downloaded from the public cache) must have the
manifest's SHA-256, be named by its stock Lake content hash, and extract with stock leantar.
Only then does the job, in the environment `ci-cache-publish` (deployable from `main` only),
read `R2_ACCOUNT_TOKEN` and write the new artifacts, the map, the manifest and the record, each
with `If-None-Match`, so nothing is overwritten. A second fresh runner then runs
`lake exe cache get` on the commit, and `lake build --no-build` must succeed. A manual run
(`workflow_dispatch`, inputs `sha`, optionally `run_id`, and `publish`) publishes any successful
self-hosted build of a given commit, or with `publish` false only verifies it. After this,
`python3 scripts/ci-cache-get.py --print-identity`, run on a published commit, gives new contents
for `scripts/cache-baseline.json`, which is only needed if the history to the newest record is
longer than 200 commits.

The publisher cannot check that an artifact is what a module's input hash produces: that would
need building it. So the cache trusts the self-hosted runner's builds, as it trusted the hand
publisher's builds before.

## Self-hosted merge queue runner

The runner host holds no credential of the project, and builds only code that is queued to land
on `main` or already on it. Its setup is in `scripts/runner/`:

- `setup-host.sh` (run as root, idempotent) creates the unprivileged user `ghrunner` (no sudo,
  no other groups), installs a pinned, checksummed copy of the GitHub Actions runner owned by
  root, blocks the metadata service and private address ranges for `ghrunner`'s uid on IPv4 and
  IPv6 (`ghrunner-firewall.service`, iptables owner rules), sets `kernel.yama.ptrace_scope=1`, and
  installs `rh-runner.service`.
- `loop.sh` (that service) runs one ephemeral just-in-time runner per job. For each job it gives
  `ghrunner` a new, empty home directory with a fresh copy of the runner, runs it in a transient
  systemd unit (read-only system, other home directories and `/srv` hidden, private `/tmp`, no new
  privileges, and the same addresses denied to the unit's cgroup), and after the job kills
  whatever is left and deletes the home directory, workspace included.
- `job-started.sh` is the runner's job-started hook. Pull requests can change the workflow they
  run, so one could ask for this runner; the hook fails every job before it starts unless it is
  `build.yml` of this repository for a `merge_group` on `main`'s queue, a push to `main`, or a
  `workflow_dispatch` (which needs write access).
- `mint-jit.sh` runs every minute on a trusted workstation whose `gh` is logged in as a
  repository admin (a systemd user timer). It keeps four one-time runner configurations from
  `POST /repos/{owner}/{repo}/actions/runners/generate-jitconfig` (labels `self-hosted`, `linux`,
  `rh-big`) in the host's root-only spool, and deletes those older than 20 hours with their
  registrations. Each configuration can register one runner for one job, and is good for nothing
  else, so the host never holds a GitHub token. If the workstation stops, the host runs the jobs
  its spool still allows (four, within 20 hours), then waits.

## Tau Ceti

The project depends on [Tau Ceti](https://github.com/TauCetiProject/TauCeti), pinned at a
toolchain tag in `lakefile.toml`. Tau Ceti publishes its oleans in its own public cache, the
service `tauceti-public` in `lakefile.toml`, which neither Mathlib's cache nor this project's
covers. `scripts/tauceti-cache-get.py`, which `lake exe cache get` (and CI) runs after Mathlib's
cache:

- stops unless Tau Ceti's own `lake-manifest.json` pins the same Mathlib commit as ours, since
  otherwise none of its cached oleans match;
- stops if `src/Statements.lean`, `src/Main.lean` or `Challenge.lean` imports a Tau Ceti module,
  so that the five statements keep depending on Mathlib alone;
- downloads Tau Ceti's mappings for the pinned revision (about 135 MB the first time);
- runs `lake build` on the Tau Ceti modules imported under `src`, which downloads exactly the
  oleans they need into `.lake/packages/TauCeti`.

After adding an import of a new Tau Ceti module, rerun `lake exe cache get`; otherwise Lake
compiles that module and its Tau Ceti dependencies from source. The Tau Ceti and Mathlib pins move
together: pick the Tau Ceti tag for the new Lean release, and check that its manifest pins the
Mathlib commit chosen here. A change of either pin changes the build inputs of every module that
imports Tau Ceti, directly or not.

For a con-leche `--compare` run, Tau Ceti's `.lake/packages/TauCeti/.lake/build/lib/lean` belongs
on the untrusted `--search-path`, with the project's, so that its declarations are checked rather
than trusted.

## Keys

The keys in the bucket behind https://rh-cache.taucetiproject.org are shared with the `grh/`
project of branch `grh-lean-cache`, which has the same modules:

- `artifacts/leanprover-community/riemann-hypothesis-grh-lean/grh/<hash>.art`: Lake's `.ltar` files,
  named by Lake's content hash;
- `grh-lean/grh/inputs/<fingerprint>.json`: the record for one set of build inputs (Git tree of
  `src`, `lakefile.toml`, `lake-manifest.json` and toolchain);
- `grh-lean/grh/maps/<sha256>.jsonl` and `grh-lean/grh/module-manifests/<sha256>.jsonl.gz`: Lake's
  map and the list of modules, with the SHA-256 of every artifact.

The keys of the earlier `main` branch's cache are separate and unchanged.
