#!/usr/bin/env bash
# Create a git worktree for a task, sharing the prebuilt Mathlib packages and seeding the build
# directory with a copy of the main build (so the vendored OC library is not rebuilt).
# Usage: scripts/new_worktree.sh <name> [base-ref]   (creates ../wt-ff/<name> on branch impl/<name>)
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"
base="${2:-HEAD}"
wt="$(dirname "$root")/wt-ff/$name"
git -C "$root" worktree add -q -b "impl/$name" "$wt" "$base"
mkdir -p "$wt/.lake"
ln -s "$root/.lake/packages" "$wt/.lake/packages"
if [ -d "$root/.lake/build" ]; then cp -r "$root/.lake/build" "$wt/.lake/build"; fi
echo "$wt"
