# prim-parser benchmarks

Benchmark parser performance with [hyperfine](https://github.com/sharkdp/hyperfine).

## Usage

```bash
./run.sh                 # current branch vs main
./run.sh my-branch main  # explicit refs
./run.sh HEAD -          # single ref (no comparison), e.g. for CI tracking
SIZE=5000 RUNS=20 WORKLOADS=json ./run.sh
```

Env vars: `WORKLOADS` (`json arith csv`), `SIZE` (2000), `ITERS` (200),
`WARMUP` (3), `RUNS` (10), `KEEP` (1, set 0 to drop worktrees), `SHARE` (1;
set 0 when refs pin different toolchain/Mathlib versions).
Results land in `results/`.

## How it works

Per ref, `run.sh` checks it out into a detached worktree, symlinks the main
checkout's `.lake/packages` (so only prim-parser recompiles, not Mathlib),
builds `Bench.lean` as a `bench` executable, then runs hyperfine on the
binaries. Worktrees are reused for incremental rebuilds.

`Bench.lean` is `bench <workload> <size> <iters>` (json/arith/csv); it builds
the input once and reparses it `iters` times. It must use API common to both
refs. Requires `hyperfine` and a working `lake build` in the main checkout.
