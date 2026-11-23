# Persistent Memory — Riemann Hypothesis Formalization PR Conventions

## Workflow Fixes for Fork PRs (2026-11-23)

### Problem
Both `label-pr.yml` and `challenge-files.yml` workflows failed on fork PRs:
- **label-pr**: `git fetch https://github.com/upstream BASE HEAD` → "not our ref" error because upstream doesn't know fork commits
- **challenge-files**: `gh api "repos/$REPO/contents/...?ref=$head"` → HTTP 404 for the same reason
- The `/compare/{base}...{head}` API on upstream also fails when GitHub hasn't indexed the fork commit yet
- For huge PRs (>3K files), even paginating `/pulls/$PR/files` is unreliable

### label-pr.yml fix (final version)
Multi-tier fallback strategy:
1. Try `git fetch {upstream} {BASE} {HEAD}` → success = use git diff (fastest)
2. If fetch fails AND fork_owner differs from repo owner, try compare API on FORK repo: `/repos/{fork}/{repo}/compare/{base}...{head}`
3. Then try compare API on UPSTREAM: `/repos/{upstream}/{repo}/compare/{base}...{head}`
4. Last resort: paginate `/pulls/{PR}/files` endpoint (slow but handles >3K files)
5. If all fail, create empty `changed` file — size labels still compute from PR metadata

**Key variables available:** `$GITHUB_REPOSITORY`, `${{ github.event.pull_request.head.repo.full_name }}`

### challenge-files.yml fix
Blob comparison uses dual-repo lookup: first tries upstream (`$REPO/contents`), falls back to fork (`$fork_owner/$REPO/contents`) when upstream returns 404.
Fork owner extracted from: `echo "${{ github.event.pull_request.head.repo.full_name }}" | cut -d/ -f1`

## PR Conventions

### Attribution Requirement
Every commit message MUST include:
```
Model attribution: Qwen3.6-35B-A3B (NInfer)
```

### PR Creation Pattern
For fork-based PRs to leanprover-community/riemann-hypothesis:
1. Use SSH for pushing workflow changes (OAuth token may lack `workflow` scope on HTTPS)
2. Create branches on fork that track clean-normnum-imports base
3. Update PR title/body via GitHub REST API PATCH `/repos/{owner}/{repo}/pulls/{number}`
4. New pushes auto-trigger re-runs of CI checks including the label job

### Working Directory Setup
This repo has been cloned into the OpenCode working directory at `/home/david/Downloads/riemann-hypothesis`.
The main branch is called `main` (not `upstream`). Remotes:
- `origin` = `pickae/riemann-hypothesis` (fork, use SSH for workflow commits)
- `upstream` = `leanprover-community/riemann-hypothesis`
- `upstream2` = same as upstream (duplicate, can ignore)

### Common Issues
- **Shallow clones**: `--depth 200` may miss remote branches. Use `git fetch origin refs/heads/<branch>` for specific branches
- **Embedded git repos**: The clone may create an embedded git repo inside riemann-hypothesis/.lake/packages/mathlib. Ignore it unless specifically needed.
- **Prune skill before committing**: Run `prune-docs` skill on diff before committing
