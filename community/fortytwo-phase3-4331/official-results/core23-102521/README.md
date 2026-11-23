# Core 23 · Playground submission #102521

Playground awarded **56.209150** to this proof of arithmetic Hilbert–Samuel from principalisation. At 22:49 UTC on November 23, 2026, it ranked first, **6.209150 points** ahead of #99885 (50.000000). [Official submission](https://play.bohrium.com/submission/102521) · [Core 23 leaderboard](https://play.bohrium.com/api/challenges/lean-4-verification-rh-core-pillar-23-arithmetic-h-3025a41d/attempts?sort=score&limit=20&page=1)

The scored source uses **11,454 Lean files and 24,784,628 normalized tokens**, down from 47,617,266. The hosted grader counted 82,934,551 characters. The local Comparator and Lean 4.33.1 default kernel accepted the exact target. [Verification record](core23/verification.json)

Levent Alpöge authored the original formalization. Fortytwo Engine: Deepseek Flash V4.1 1017 contributed proof reductions in four modules about the arithmetic Hilbert–Samuel implication, generating sections away from a finite set, restricting an induced model to a dominant curve, and isometric shifts. Codex placed the four edited source bodies and their dependent modules in `Solution.lean` in dependency order, sharing one import list. The resulting layout incorporates 41 upstream modules and the target wrapper. The remaining 11,453 files are byte-identical to their released versions. [Winning Lean source](core23/Solution.lean) · [Per-module source hashes](core23/verification.json)

## Reconstruct the scored source tree

Download the organizer’s Core 23 shard. In this directory, run the following command with Python 3.14 and choose a new output path. [Official Core 23 shard](https://github.com/Osgood001/riemann-hypothesis/releases/download/v2026.11.23-shards/core23.tar.zst)

```sh
python3.14 reconstruct.py 23 /path/to/core23.tar.zst /tmp/core23-attempt-102521
```

The command checks the shard’s SHA-256, reconstructs all 11,454 files and checks the complete source-tree SHA-256, `06f0494c4deac6650ff68e38ba3ad1bcddd154c5f018c7692cb1b33a74218532`.
