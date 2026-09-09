#!/usr/bin/env bash
# Repo content must not reference local paths (absolute home directories).
# Worktrees are ephemeral and machine-local; `_tmp/` is a repo-relative,
# gitignored artifact directory and is allowed.
set -u
cd "$(dirname "$0")/.."
bad=$(git grep -n -E '/home/[a-z]' -- . ':!tests/no-local-paths.sh' || true)
if [ -n "$bad" ]; then
  echo "no-local-paths: FAIL — absolute home paths in tracked files:"
  echo "$bad" | head -20
  exit 1
fi
echo "no-local-paths: OK"
