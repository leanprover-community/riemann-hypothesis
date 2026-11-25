# Build cache

This branch is the readable edition (`grh/`) of https://github.com/lsernau/grh-lean commit
72fead102f663d5c7a407964a13dc0cf9d977207, moved to the repository root, plus configuration and
scripts for a shared build cache. No file under `src`, and no `Challenge.lean`, `comparator.json`,
`lake-manifest.json` or `lean-toolchain`, is changed. The additions are `CACHE.md`, a note at the
top of `README.md`, the marked lines in `lakefile.toml`, `Cache.lean`, `lake-cache-get.sh`,
`ci-cache-get.py`, `fetch-artifacts.py`, `cache-baseline.json` and `tests/` in `scripts`, and the
workflow `.github/workflows/build.yml`. The scripts are copied or adapted from
`scripts/` of the earlier `main` branch of https://github.com/leanprover-community/riemann-hypothesis
(now the branch `alpoge`).

**The cached files were built from an unverified third-party proof, and the cache does not verify
anything.** The checks in the scripts only establish that you have the bytes which were published
for your exact build inputs. To check the proof, build it from source yourself, without this cache.

## Use

    lake exe cache get
    lake build

This needs Python 3.11 or newer and curl 7.71 or newer, and no credential. It fetches Mathlib's
cache, then this project's, and unpacks it. It ends with `lake build --no-build`, which must report
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

`.github/workflows/build.yml` builds every pull request to `main`, and every push to `main`, on a
GitHub-hosted runner, with the exact record if there is one and the baseline otherwise. It fails
if `lake build` fails, if the build log has Lean's warning that a declaration uses `sorry`, or if
`scripts/PrintAxioms.lean` reports any axiom other than `propext`, `Classical.choice` and
`Quot.sound` for the five theorems. It only reads the cache and publishes nothing.

Records are published by hand, so the baseline falls behind `main` as pull requests are merged,
and builds get slower: each one also compiles everything that changed on `main` since the
newest published record. A change to a module that most of `src` imports (`Lib.Base`, for
example) compiles all 803 modules, about 4 hours of module build time: one to two hours on the 4
cores of `ubuntu-latest`.
The proposed follow-up is a separate job that, on pushes to `main` only, builds `main` and
publishes its record, map, module manifest and artifacts with credentials that pull requests
never see. After a publish by hand, `python3 scripts/ci-cache-get.py --print-identity`, run on the
published commit, gives the new contents of `scripts/cache-baseline.json`.

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
