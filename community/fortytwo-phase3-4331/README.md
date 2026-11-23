# Fortytwo Phase 3 proof reductions

These source changes reduce the size of Levent Alpöge’s Phase 3 proofs. Fortytwo Engine: Deepseek Flash V4.1 1017 contributed proofs through DeepSeek Harness. Codex supervised the campaign and contributed dependency analysis and proof edits. Each core’s verification file identifies its contributions. Keith Adler’s published dependency-pruning analysis informed the search.

Levent Alpöge authored the original Core 37 formalization. Codex reduced the Bernstein–Zelevinsky finite-length proof by narrowing dependencies in two modules. Fortytwo conducted the preceding search and verified the parent proof. Its edit to ExampleSatisfiesConditionsAtFive falls outside this 74-file import closure. The independent local Comparator and Lean default kernel accepted this source-only study.

Levent Alpöge authored the original Core 40 proof. Codex extracted the five source modules and verified the resulting six-file reduction. Fortytwo contributed the earlier search and verified parent proof. Its LiftErrorLocal edit falls outside this final import closure. The six-file result has a local Comparator and kernel verification.

| Core | Editable Lean files | Baseline tokens | Verified local tokens | Tokens saved |
| ---: | ---: | ---: | ---: | ---: |
| 14 | 1,121 | 3,467,872 | 2,150,099 | 1,317,773 |
| 15 | 28,473 | 60,808,488 | 47,870,200 | 12,938,288 |
| 17 | 30,501 | 48,886,000 | 48,885,898 | 102 |
| 18 | 33,702 | 75,331,745 | 74,343,508 | 988,237 |
| 22 | 20,228 | 38,808,445 | 38,806,732 | 1,713 |
| 23 | 10,958 | 47,617,266 | 23,408,674 | 24,208,592 |
| 24 | 12,996 | 30,828,159 | 26,697,100 | 4,131,059 |
| 25 | 10,649 | 29,435,752 | 24,600,777 | 4,834,975 |
| 26 | 242 | 540,118 | 366,542 | 173,576 |
| 28 | 173 | 920,317 | 397,815 | 522,502 |
| 29 | 122 | 831,319 | 341,451 | 489,868 |
| 33 | 42 | 826,075 | 74,366 | 751,709 |
| 34 | 188 | 400,204 | 239,570 | 160,634 |
| 37 | 74 | 1,852,115 | 256,560 | 1,595,555 |
| 40 | 6 | 1,031,987 | 2,677 | 1,029,310 |

The independent Comparator and the Lean 4.33.1 default kernel accepted each exact target with `propext`, `Quot.sound` and `Classical.choice`. Each directory records the local replay, complete source-tree digest, Mathlib revision and the checksums of its original sources. The local check derived the protected boundary from the organizer’s published frozen roots. The table reports locally measured token counts.

## Reproduce the proof sources

Download the `coreN.tar.zst` archive linked in the core’s `verification.json`. From this directory, run the command with Python 3.14 and Git installed. Choose a new output directory.

```sh
python3.14 reconstruct.py 24 /path/to/core24.tar.zst /tmp/fortytwo-core24/proof
```

The script checks the archive, applies the Lean edits, follows imports within the editable shard and verifies the resulting source tree. Use the reconstructed `proof/` directory in the core’s pinned Lean challenge environment.
Fast cores record their upstream Git revision and per-file SHA-256 values in `verification.json`. Pass the upstream checkout’s `src` directory as the second argument, for example `python3.14 reconstruct.py 26 /path/to/riemann-lean/src /tmp/core26-proof`.

[Organizer source shards](https://github.com/Osgood001/riemann-hypothesis/releases/tag/v2026.11.23-shards)
