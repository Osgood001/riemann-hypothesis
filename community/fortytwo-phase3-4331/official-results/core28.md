# Core 28 · Fundamental-domain point bound

Playground confirmed **58.126391** for submission **#102563** at 23:10 UTC on 2026-11-23. At that check it ranked first, 0.076887 points ahead of #102547. [Official submission](https://play.bohrium.com/submission/102563) · [Core 28 leaderboard](https://play.bohrium.com/api/challenges/lean-4-verification-rh-fast-sub-pillar-28-fundamen-7b3737ce/attempts?sort=score&limit=20&page=1)

Each submission preserves Levent Alpöge’s statement that the Fundamental-domain point bound have finite length. Each revision links to the source that received its score. The token counts come from the pinned verification environment.

| Submission | Official final score | Recorded standing | Verified tokens | Lean files | Exact scored source |
| --- | ---: | --- | ---: | ---: | --- |
| [#102510](https://play.bohrium.com/submission/102510) | 56.288733 | First | 474,458 | 217 | [`2ae8d801b062`](https://github.com/vlarin/riemann-hypothesis/tree/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28) |
| [#102518](https://play.bohrium.com/submission/102518) | 57.462438 | First | 410,274 | 176 | [`a498604f1b7b`](https://github.com/vlarin/riemann-hypothesis/tree/a498604f1b7b717ae9315ba63ed8efc904becb0f/community/fortytwo-phase3-4331/core28) |
| [#102529](https://play.bohrium.com/submission/102529) | 57.703401 | First | 397,815 | 173 | [`aac6e7ae2ee3`](https://github.com/vlarin/riemann-hypothesis/tree/aac6e7ae2ee3160b984992c5b52634b81f5a2b74/community/fortytwo-phase3-4331/core28) |
| [#102537](https://play.bohrium.com/submission/102537) | 57.925535 | First | 386,544 | 173 | [`0fca09d75ba5`](https://github.com/vlarin/riemann-hypothesis/tree/0fca09d75ba5ce47118dfdccdb3d4052b53dd7c8/community/fortytwo-phase3-4331/core28) |
| [#102547](https://play.bohrium.com/submission/102547) | 58.049504 | First | 380,343 | 170 | [`e010d2b2088d`](https://github.com/vlarin/riemann-hypothesis/tree/e010d2b2088d46f39f996a6fc0d178644eac2559/community/fortytwo-phase3-4331/core28) |
| [#102563](https://play.bohrium.com/submission/102563) | 58.126391 | First | 376,529 | 170 | [`7c45d522c5dc`](https://github.com/vlarin/riemann-hypothesis/tree/7c45d522c5dce2aa274fcc6db0df3374277d3ba2/community/fortytwo-phase3-4331/core28) |

## Changes in the scored proofs

Levent Alpöge authored the Fourier sign, contour-independence and coefficient-bound lemmas and the original formalization. Fortytwo Engine: Deepseek Flash V4.1 1017 removed the single import `FourSignHolds` in `FractionalSliceDomains.lean`. Each scored revision below retains the exact Fortytwo-authored file. Codex made the accompanying recipient-specific edits and verified the resulting source trees. The independent Comparator and Lean 4.33.1 default kernel accepted each target.

- **#102510** Codex imported `FourIndep` and `FourBasic` directly where coefficient positivity is proved. It supplied Alpöge’s contour-independence lemma `four_indep` and coefficient bound `four_bound` to `four_sign`. Together with Fortytwo’s import removal this saved 445,859 tokens against the baseline. The hosted grader counted 217 files and 1,539,511 characters. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102518** Codex narrowed `LatAll` to `Closed.approx` and its two dependencies, keeping the original approximation proof. This saved 64,184 further tokens and 41 files against #102510. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/a498604f1b7b717ae9315ba63ed8efc904becb0f/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102529** Codex retained the six original Fourier declarations needed in the support module and imported their Mathlib dependencies directly. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/aac6e7ae2ee3160b984992c5b52634b81f5a2b74/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102537** Codex retained the torus projection and lift, the normalized bounds and positivity lemmas for sections, and the majorant transfer along the real flow. It removed later results unused by the target, saving a further 11,271 tokens. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/0fca09d75ba5ce47118dfdccdb3d4052b53dd7c8/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102547** Codex removed unused imports for trace-form independence and weighted telescoping sums. The proof retained Alpöge’s transfer, nonnegativity and zero lemmas for the Fourier majorant. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/e010d2b2088d46f39f996a6fc0d178644eac2559/community/fortytwo-phase3-4331/core28/changes.patch)

- **#102563** Codex restricted the conjugation and isotropic-flow modules to the proofs used for integral conjugation, the rank-one flow action, column transport and linearity. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/7c45d522c5dce2aa274fcc6db0df3374277d3ba2/community/fortytwo-phase3-4331/core28/changes.patch)
