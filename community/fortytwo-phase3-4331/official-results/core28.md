# Core 28 · Fundamental-domain point bound

Playground confirmed **56.288733** for submission **#102510** at 21:50 UTC on 2026-11-23. At that check it ranked first, 6.288733 points ahead of #101420. [Official submission](https://play.bohrium.com/submission/102510) · [Core 28 leaderboard](https://play.bohrium.com/api/challenges/lean-4-verification-rh-fast-sub-pillar-28-fundamen-7b3737ce/attempts?sort=score&limit=20&page=1)

Each submission preserves Levent Alpöge’s statement that the Fundamental-domain point bound have finite length. Each revision links to the source that received its score. The token counts come from the pinned verification environment.

| Submission | Official final score | Recorded standing | Verified tokens | Lean files | Exact scored source |
| --- | ---: | --- | ---: | ---: | --- |
| [#102510](https://play.bohrium.com/submission/102510) | 56.288733 | First | 474,458 | 217 | [`2ae8d801b062`](https://github.com/vlarin/riemann-hypothesis/tree/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28) |

## Changes in the scored proofs

Levent Alpöge authored the Fourier sign, contour-independence and coefficient-bound lemmas and the original formalization. Fortytwo Engine: Deepseek Flash V4.1 1017 removed the single import `FourSignHolds` in `FractionalSliceDomains.lean`. Each scored revision below retains the exact Fortytwo-authored file. Codex made the accompanying recipient-specific edits and verified the resulting source trees. The independent Comparator and Lean 4.33.1 default kernel accepted each target.

- **#102510** Codex imported `FourIndep` and `FourBasic` directly where coefficient positivity is proved. It supplied Alpöge’s contour-independence lemma `four_indep` and coefficient bound `four_bound` to `four_sign`. Together with Fortytwo’s import removal this saved 445,859 tokens against the baseline. The hosted grader counted 217 files and 1,539,511 characters. [Source changes](https://github.com/vlarin/riemann-hypothesis/blob/2ae8d801b0625f4b66e07118b7f0f02a4c45f942/community/fortytwo-phase3-4331/core28/changes.patch)
