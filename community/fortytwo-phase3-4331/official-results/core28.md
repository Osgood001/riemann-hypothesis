# Core 28 · Fundamental-domain point bound

Playground confirmed **59.459158** for submission **#102720** at 01:13 UTC on 2026-11-24. At that check it ranked first, 0.211026 points ahead of #102700. [Official submission](https://play.bohrium.com/submission/102720) · [Core 28 leaderboard](https://play.bohrium.com/api/challenges/lean-4-verification-rh-fast-sub-pillar-28-fundamen-7b3737ce/attempts?sort=score&limit=20&page=1)

Each submission preserves Levent Alpöge’s statement that the Fundamental-domain point bound have finite length. Each revision links to the source that received its score. The token counts come from the pinned verification environment.

| Submission | Official final score | Recorded standing | Verified tokens | Lean files | Exact scored source |
| --- | ---: | --- | ---: | ---: | --- |
| [#102510](https://play.bohrium.com/submission/102510) | 56.288733 | First | 474,458 | 217 | [`2ae8d801b062`](https://github.com/vlarin/riemann-hypothesis/tree/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28) |
| [#102518](https://play.bohrium.com/submission/102518) | 57.462438 | First | 410,274 | 176 | [`a498604f1b7b`](https://github.com/vlarin/riemann-hypothesis/tree/a498604f1b7b717ae9315ba63ed8efc904becb0f/community/fortytwo-phase3-4331/core28) |
| [#102529](https://play.bohrium.com/submission/102529) | 57.703401 | First | 397,815 | 173 | [`aac6e7ae2ee3`](https://github.com/vlarin/riemann-hypothesis/tree/aac6e7ae2ee3160b984992c5b52634b81f5a2b74/community/fortytwo-phase3-4331/core28) |
| [#102537](https://play.bohrium.com/submission/102537) | 57.925535 | First | 386,544 | 173 | [`0fca09d75ba5`](https://github.com/vlarin/riemann-hypothesis/tree/0fca09d75ba5ce47118dfdccdb3d4052b53dd7c8/community/fortytwo-phase3-4331/core28) |
| [#102547](https://play.bohrium.com/submission/102547) | 58.049504 | First | 380,343 | 170 | [`e010d2b2088d`](https://github.com/vlarin/riemann-hypothesis/tree/e010d2b2088d46f39f996a6fc0d178644eac2559/community/fortytwo-phase3-4331/core28) |
| [#102563](https://play.bohrium.com/submission/102563) | 58.126391 | First | 376,529 | 170 | [`7c45d522c5dc`](https://github.com/vlarin/riemann-hypothesis/tree/7c45d522c5dce2aa274fcc6db0df3374277d3ba2/community/fortytwo-phase3-4331/core28) |
| [#102579](https://play.bohrium.com/submission/102579) | 58.274947 | First | 369,229 | 170 | [`ca030c67cd2b`](https://github.com/vlarin/riemann-hypothesis/tree/ca030c67cd2b5dd018752613d9c512b12a9b7cbe/community/fortytwo-phase3-4331/core28) |
| [#102588](https://play.bohrium.com/submission/102588) | 58.703503 | First | 348,678 | 165 | [`ba388c7babe7`](https://github.com/vlarin/riemann-hypothesis/tree/ba388c7babe7980c4217d5200bcea695f6f3841f/community/fortytwo-phase3-4331/core28) |
| [#102602](https://play.bohrium.com/submission/102602) | 58.938202 | First | 337,741 | 161 | [`253beb7c689b`](https://github.com/vlarin/riemann-hypothesis/tree/253beb7c689b546b921c51afa4df3e7f49e71a9b/community/fortytwo-phase3-4331/core28) |
| [#102624](https://play.bohrium.com/submission/102624) | 59.123959 | First | 329,243 | 154 | [`57b69d131e16`](https://github.com/vlarin/riemann-hypothesis/tree/57b69d131e16c92677b8b8dfa9d2f73fedad832b/community/fortytwo-phase3-4331/core28) |
| [#102646](https://play.bohrium.com/submission/102646) | 59.171290 | First | 327,100 | 154 | [`39b89d5afbc3`](https://github.com/vlarin/riemann-hypothesis/tree/39b89d5afbc30ce9f566befee18c0f5a264295ab/community/fortytwo-phase3-4331/core28) |
| [#102700](https://play.bohrium.com/submission/102700) | 59.248132 | First | 323,640 | 154 | [`ea53dc631381`](https://github.com/vlarin/riemann-hypothesis/tree/ea53dc631381a2c0e3e745af74f80d7ea0e9cee0/community/fortytwo-phase3-4331/core28) |
| [#102720](https://play.bohrium.com/submission/102720) | 59.459158 | First | 314,260 | 154 | [`eee48f5e0091`](https://github.com/vlarin/riemann-hypothesis/tree/eee48f5e00911bdc3962816acc37ca25066e6627/community/fortytwo-phase3-4331/core28) |

## Changes in the scored proofs

Levent Alpöge authored the Fourier sign, contour-independence and coefficient-bound lemmas and the original formalization. Fortytwo Engine: Deepseek Flash V4.1 1017 removed the single import `FourSignHolds` in `FractionalSliceDomains.lean`. Each scored revision below retains the exact Fortytwo-authored file. Codex made the accompanying recipient-specific edits and verified the resulting source trees. The independent Comparator and Lean 4.33.1 default kernel accepted each target.

- **#102510** Codex imported `FourIndep` and `FourBasic` directly where coefficient positivity is proved. It supplied Alpöge’s contour-independence lemma `four_indep` and coefficient bound `four_bound` to `four_sign`. Together with Fortytwo’s import removal this saved 445,859 tokens against the baseline. The hosted grader counted 217 files and 1,539,511 characters. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102518** Codex narrowed `LatAll` to `Closed.approx` and its two dependencies, keeping the original approximation proof. This saved 64,184 further tokens and 41 files against #102510. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/a498604f1b7b717ae9315ba63ed8efc904becb0f/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102529** Codex retained the six original Fourier declarations needed in the support module and imported their Mathlib dependencies directly. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/aac6e7ae2ee3160b984992c5b52634b81f5a2b74/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102537** Codex retained the torus projection and lift, the normalized bounds and positivity lemmas for sections, and the majorant transfer along the real flow. It removed later results unused by the target, saving a further 11,271 tokens. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/0fca09d75ba5ce47118dfdccdb3d4052b53dd7c8/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102547** Codex removed unused imports for trace-form independence and weighted telescoping sums. The proof retained Alpöge’s transfer, nonnegativity and zero lemmas for the Fourier majorant. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/e010d2b2088d46f39f996a6fc0d178644eac2559/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102563** Codex restricted the conjugation and isotropic-flow modules to the proofs used for integral conjugation, the rank-one flow action, column transport and linearity. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/7c45d522c5dce2aa274fcc6db0df3374277d3ba2/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102579** Codex proved two coefficient product bounds using `log x ≤ x − 1`. It also bounded `exp (9/4)` by fourth powers and proved differentiability in the two chart cases using finite sums. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/ca030c67cd2b5dd018752613d9c512b12a9b7cbe/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102588** Codex specialized the near-supremum argument to bounded Fourier sections. The sign theorem and flow norm ratio gave index nonnegativity, allowing the proof to omit the earlier polynomial-growth comparisons and exponential-decay estimate. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/ba388c7babe7980c4217d5200bcea695f6f3841f/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102602** Codex proved index nonnegativity on an admissible imaginary ray using Alpöge’s complexified flow-character identity. A negative index would grow exponentially along that ray, contradicting the polynomial bound from the flow norm ratio. This removed four support modules and saved 10,937 tokens against #102588. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/253beb7c689b546b921c51afa4df3e7f49e71a9b/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102624** Codex kept the five unipotent-majorant conclusions needed for the frame move and reused Alpöge’s orthonormal-majorant comparison. A localization-span result supplies a single denominator for the entire lattice vector, eliminating a second span induction. This removed seven files and 8,498 normalized tokens from #102602. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/57b69d131e16c92677b8b8dfa9d2f73fedad832b/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102646** Codex proved one Fourier-character estimate along admissible isotropic rays and applied it to both embedded directions and unipotent vector coefficients. Together with a shared discrete-flow variation argument, this saved 2,143 normalized tokens over #102624. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/39b89d5afbc30ce9f566befee18c0f5a264295ab/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102700** Codex descended the periodic cube integrand to the unit torus and used translation invariance of its normalized Haar measure. It also bounded an off-diagonal entry using positivity of the two-by-two determinant and the arithmetic–geometric mean inequality. These and accompanying height and decay reductions saved 3,460 normalized tokens over #102646. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/ea53dc631381a2c0e3e745af74f80d7ea0e9cee0/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102720** Codex replaced repeated expansions of the Hermitian form with Alpöge’s left-linearity and right conjugate-linearity identities. It assembled the unipotent vector-group action from the matrix multiplication, determinant, unitarity and flow formulas already available, and used the Fourier–Jacobi integral bound in the coefficient estimate. This saved 9,380 normalized tokens over #102700. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/eee48f5e00911bdc3962816acc37ca25066e6627/community/fortytwo-phase3-4331/core28/changes.patch)
