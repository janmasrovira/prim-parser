#!/usr/bin/env bash
#
# Benchmark prim-parser with hyperfine.
#
#   bench/run.sh [REF_A] [REF_B]
#
# Defaults: REF_A = current branch, REF_B = main. Pass "-" (or "") as REF_B to
# benchmark REF_A alone (single-ref mode, e.g. for CI tracking on main).
#
# Each ref is built as a `bench` executable in its own git worktree, then
# hyperfine times the binaries per workload (comparing the two, or just REF_A).
#
# Tunables (environment variables):
#   WORKLOADS  space-separated subset of "json arith csv"   (default: all)
#   SIZE       problem size per workload                     (default: 2000)
#   ITERS      reparses per process invocation               (default: 200)
#   WARMUP     hyperfine warmup runs                          (default: 3)
#   RUNS       hyperfine measured runs                        (default: 10)
#   KEEP       keep worktrees after the run                   (default: 1)
#   SHARE      symlink the main checkout's built .lake/packages (default: 1);
#              set 0 when refs pin different toolchain/Mathlib versions
#
set -euo pipefail

REPO="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
BENCH_DIR="$REPO/bench"
WORKTREE_ROOT="$BENCH_DIR/.worktrees"
RESULTS_DIR="$BENCH_DIR/results"

REF_A="${1:-$(git -C "$REPO" rev-parse --abbrev-ref HEAD)}"
REF_B="${2-main}"
SINGLE=0
case "$REF_B" in ""|"-") SINGLE=1 ;; esac

WORKLOADS="${WORKLOADS:-json arith csv}"
SIZE="${SIZE:-2000}"
ITERS="${ITERS:-200}"
WARMUP="${WARMUP:-3}"
RUNS="${RUNS:-10}"
KEEP="${KEEP:-1}"
SHARE="${SHARE:-1}"

command -v hyperfine >/dev/null || { echo "error: hyperfine not found on PATH" >&2; exit 1; }
[ -d "$REPO/.lake/packages" ] || {
  echo "error: $REPO/.lake/packages missing — run 'lake build' (and 'lake exe cache get') in the main checkout first" >&2
  exit 1
}

# Turn a ref into a filesystem-safe slug.
slug() { printf '%s' "$1" | tr '/ ' '__'; }

# Build the `bench` executable for a ref inside its worktree; echo the binary path.
build_ref() {
  local ref="$1"
  local wt="$WORKTREE_ROOT/$(slug "$ref")"
  local rev
  rev="$(git -C "$REPO" rev-parse "$ref")"

  echo ">>> $ref ($rev)" >&2

  # Reuse the worktree if already at $rev (incremental); else (re)create it.
  # Detached checkouts avoid the "branch already checked out" conflict.
  if [ -d "$wt/.git" ] || [ -f "$wt/.git" ]; then
    if [ "$(git -C "$wt" rev-parse HEAD 2>/dev/null)" != "$rev" ]; then
      git -C "$wt" checkout --quiet --detach --force "$rev"
    fi
  else
    git -C "$REPO" worktree remove --force "$wt" 2>/dev/null || true
    rm -rf "$wt"
    git -C "$REPO" worktree add --quiet --force --detach "$wt" "$rev"
  fi

  # SHARE=1: reuse the main checkout's built deps; SHARE=0: fetch this ref's own.
  mkdir -p "$wt/.lake"
  if [ "$SHARE" = "1" ]; then
    ln -sfn "$REPO/.lake/packages" "$wt/.lake/packages"
  else
    [ -L "$wt/.lake/packages" ] && rm -f "$wt/.lake/packages"
    ( cd "$wt" && lake exe cache get ) >&2 || true
  fi

  cp "$BENCH_DIR/Bench.lean" "$wt/Bench.lean"
  if ! grep -q 'name = "bench"' "$wt/lakefile.toml"; then
    printf '\n[[lean_exe]]\nname = "bench"\nroot = "Bench"\n' >> "$wt/lakefile.toml"
  fi

  ( cd "$wt" && lake build bench ) >&2

  echo "$wt/.lake/build/bin/bench"
}

mkdir -p "$RESULTS_DIR"

EXE_A="$(build_ref "$REF_A")"
[ "$SINGLE" = 0 ] && EXE_B="$(build_ref "$REF_B")"

echo
if [ "$SINGLE" = 1 ]; then
  echo "=== hyperfine: $REF_A === (size=$SIZE iters=$ITERS)"
else
  echo "=== hyperfine: $REF_A  vs  $REF_B === (size=$SIZE iters=$ITERS)"
fi

for wl in $WORKLOADS; do
  echo
  echo "--- workload: $wl ---"
  cmds=( --command-name "$REF_A [$wl]" "$EXE_A $wl $SIZE $ITERS" )
  if [ "$SINGLE" = 1 ]; then
    out="$RESULTS_DIR/$(slug "$REF_A")_${wl}"
  else
    out="$RESULTS_DIR/$(slug "$REF_A")_vs_$(slug "$REF_B")_${wl}"
    cmds+=( --command-name "$REF_B [$wl]" "$EXE_B $wl $SIZE $ITERS" )
  fi
  hyperfine --warmup "$WARMUP" --runs "$RUNS" \
    "${cmds[@]}" --export-markdown "${out}.md" --export-json "${out}.json"
done

echo
echo "Results written to $RESULTS_DIR/"

if [ "$KEEP" != "1" ]; then
  git -C "$REPO" worktree remove --force "$WORKTREE_ROOT/$(slug "$REF_A")" 2>/dev/null || true
  [ "$SINGLE" = 0 ] && git -C "$REPO" worktree remove --force "$WORKTREE_ROOT/$(slug "$REF_B")" 2>/dev/null || true
fi
