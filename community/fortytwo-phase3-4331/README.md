# Fortytwo Phase 3 proof reductions

These four submissions narrow the dependency closure of Levent Alpöge’s Core 14, 23, 24 and 25 proofs. Fortytwo Engine: Deepseek Flash V4.1 1017 generated proof edits through DeepSeek Harness. Codex supervised assembly and independent replay. The campaign used Keith Adler’s public dependency-pruning analysis as a methodological reference.

| Core | Retained files | Published baseline tokens | Locally measured tokens | Tokens saved |
| ---: | ---: | ---: | ---: | ---: |
| 14 | 1,121 | 3,467,872 | 2,150,099 | 1,317,773 |
| 23 | 11,827 | 47,617,266 | 25,444,425 | 22,172,841 |
| 24 | 14,175 | 30,828,159 | 28,964,690 | 1,863,469 |
| 25 | 10,649 | 29,435,752 | 24,600,777 | 4,834,975 |

The independent Comparator and Lean default kernel accepted each exact target under Lean 4.33.1 and the three standard axioms. Each verification record contains the Mathlib revision, source archive checksum, replay date and digest of the complete retained source tree. The token counts are local. The local replay reconstructed each protected boundary from the organizer’s published frozen roots. The organizer’s private grader manifest was unavailable.

## Reproduce the proof sources

Download the `coreN.tar.zst` archive linked in that core’s `verification.json`. From this directory, run the command below with Python 3.14 and Git installed. The output path must be new.

```sh
python3.14 reconstruct.py 24 /path/to/core24.tar.zst /tmp/fortytwo-core24/proof
```

The script verifies the organizer’s archive, applies the changes, follows imports within the editable shard, and verifies the complete result before writing it. Use the output as the `proof/` directory in the core’s Lean 4.33.1 challenge environment. Each `changes.patch` contains the edits against the released shard. `Solution.lean` provides the target wrapper.

[Organizer source shards](https://github.com/Osgood001/riemann-hypothesis/releases/tag/v2026.11.23-shards)
