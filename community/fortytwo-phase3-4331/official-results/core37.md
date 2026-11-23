# Core 37 · Bernstein–Zelevinsky standard functors

Playground confirmed **57.446888** for submission **#102456** at 21:37 UTC on 2026-11-23. At that check it ranked first, 0.094763 points ahead of #102447. [Official submission](https://play.bohrium.com/submission/102456) · [Core 37 leaderboard](https://play.bohrium.com/api/challenges/lean-4-verification-rh-fast-sub-pillar-37-bernstei-4cf641b0/attempts?sort=score&limit=20&page=1)

Each submission preserves Levent Alpöge’s statement that the Bernstein–Zelevinsky standard functors have finite length. Each revision links to the source that received its score. The token counts come from the pinned verification environment.

| Submission | Official final score | Recorded standing | Verified tokens | Lean files | Exact scored source |
| --- | ---: | --- | ---: | ---: | --- |
| [#102363](https://play.bohrium.com/submission/102363) | 50.259329 | First | 1,808,176 | 482 | [`2718befff8fc`](https://github.com/vlarin/riemann-hypothesis/tree/2718befff8fc4bf02fc30d527eb365a52f497248/community/fortytwo-phase3-4331/core37) |
| [#102391](https://play.bohrium.com/submission/102391) | 50.419707 | First | 1,781,302 | 479 | [`f745221ef07e`](https://github.com/vlarin/riemann-hypothesis/tree/f745221ef07edcfd813840f5c4ce6aad337d98af/community/fortytwo-phase3-4331/core37) |
| [#102408](https://play.bohrium.com/submission/102408) | 56.848818 | First | 891,732 | 230 | [`faad2f1d50e7`](https://github.com/vlarin/riemann-hypothesis/tree/faad2f1d50e7fc79cb81516c67fdc1e77b5954ab/community/fortytwo-phase3-4331/core37) |
| [#102429](https://play.bohrium.com/submission/102429) | 57.094861 | First | 864,858 | 227 | [`457035409a7d`](https://github.com/vlarin/riemann-hypothesis/tree/457035409a7d31c1d4b36110a263deed69e1d2e9/community/fortytwo-phase3-4331/core37) |
| [#102441](https://play.bohrium.com/submission/102441) | 57.238835 | First | 849,371 | 226 | [`811bced7e2a8`](https://github.com/vlarin/riemann-hypothesis/tree/811bced7e2a8199e88ec5802c23fb94a9c18b171/community/fortytwo-phase3-4331/core37) |
| [#102447](https://play.bohrium.com/submission/102447) | 57.352125 | Second to #102456 | 837,308 | 226 | [`e4a9b3e32a3d`](https://github.com/vlarin/riemann-hypothesis/tree/e4a9b3e32a3d0a04a24c828f17be439a7e081fc4/community/fortytwo-phase3-4331/core37) |
| [#102456](https://play.bohrium.com/submission/102456) | 57.446888 | First | 827,301 | 226 | [`f583aa8f2a1b`](https://github.com/vlarin/riemann-hypothesis/tree/f583aa8f2a1bc666358233beed719525493107b1/community/fortytwo-phase3-4331/core37) |

## Changes in the scored proofs

Fortytwo Engine: Deepseek Flash V4.1 1017 supplied the Lean edits described below as Fortytwo contributions. Codex checked which declarations the Core 37 target uses and verified the combined sources.

- **#102363** Fortytwo trimmed the worked example at the prime five in `ExampleSatisfiesConditionsAtFive`, retaining its shared definitions and removing an import and the unused example proofs. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/2718befff8fc4bf02fc30d527eb365a52f497248/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102391** Fortytwo removed the complex-conjugation import in `QuadraticLogDerivCongr`. The downstream module still proves congruence of the quadratic logarithmic derivative. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/f745221ef07edcfd813840f5c4ce6aad337d98af/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102408** Codex retained `continuous_leviProj`, the continuity of the projection from a parabolic subgroup to its Levi factor. The module could then omit three imports and the proofs about irreducibility of induced representations. This revision uses the Fortytwo prime-five edit. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/faad2f1d50e7fc79cb81516c67fdc1e77b5954ab/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102429** The scored proof combines the Levi-projection reduction with the Fortytwo one-line removal of `GaloisMapComplexConjugation` in `QuadraticLogDerivCongr`. This removes three files and 26,874 tokens from #102408. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/457035409a7d31c1d4b36110a263deed69e1d2e9/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102441** Fortytwo removed the unused `ExistsNsmulMem` import from `JointDModelAppliesUnitLattice`. The closure lost one file and 15,487 tokens relative to #102429. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/811bced7e2a8199e88ec5802c23fb94a9c18b171/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102447** Fortytwo trimmed `SecondComplementParameterBounds`, removing unused results about places lying over a prime and conjugation of those places. The verified source saved 12,063 further tokens. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/e4a9b3e32a3d0a04a24c828f17be439a7e081fc4/community/fortytwo-phase3-4331/core37/changes.patch)

- **#102456** Fortytwo shortened `SumLogPrimeFactorsLe` by removing unused results including the change of the lattice invariant `muDef` when an ideal scales its lattice. This saved 10,007 further tokens. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/f583aa8f2a1bc666358233beed719525493107b1/community/fortytwo-phase3-4331/core37/changes.patch)
