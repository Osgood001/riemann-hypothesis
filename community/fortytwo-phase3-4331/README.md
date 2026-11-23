# Fortytwo Phase 3 proof reductions

These source changes reduce the size of Levent Alpöge’s Phase 3 proofs. Fortytwo Engine: Deepseek Flash V4.1 1017 contributed proofs through DeepSeek Harness. Codex supervised the campaign and contributed dependency analysis and proof edits. Each core’s verification file identifies its contributions. Keith Adler’s published dependency-pruning analysis informed the search.

| Core | Editable Lean files | Baseline tokens | Verified local tokens | Tokens saved |
| ---: | ---: | ---: | ---: | ---: |
| 14 | 1,121 | 3,467,872 | 2,150,099 | 1,317,773 |
| 15 | 28,473 | 60,808,488 | 47,870,200 | 12,938,288 |
| 17 | 30,501 | 48,886,000 | 48,885,898 | 102 |
| 18 | 33,702 | 75,331,745 | 74,343,508 | 988,237 |
| 23 | 10,958 | 47,617,266 | 23,408,674 | 24,208,592 |
| 24 | 14,175 | 30,828,159 | 28,964,690 | 1,863,469 |
| 25 | 10,649 | 29,435,752 | 24,600,777 | 4,834,975 |

The independent Comparator and the Lean 4.33.1 default kernel accepted each exact target with `propext`, `Quot.sound` and `Classical.choice`. Each directory records the local replay, complete source-tree digest, Mathlib revision and organizer shard checksum. The local check derived the protected boundary from the organizer’s published frozen roots. The table reports locally measured token counts.

## Reproduce the proof sources

Download the `coreN.tar.zst` archive linked in the core’s `verification.json`. From this directory, run the command with Python 3.14 and Git installed. Choose a new output directory.

```sh
python3.14 reconstruct.py 24 /path/to/core24.tar.zst /tmp/fortytwo-core24/proof
```

The script checks the archive, applies the Lean edits, follows imports within the editable shard and verifies the resulting source tree. Use the reconstructed `proof/` directory in the core’s pinned Lean challenge environment.

[Organizer source shards](https://github.com/Osgood001/riemann-hypothesis/releases/tag/v2026.11.23-shards)
