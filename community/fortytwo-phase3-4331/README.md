# Fortytwo Phase 3 proof reductions

These source changes reduce the size of Levent Alpöge’s Phase 3 proofs. Fortytwo Engine: Deepseek Flash V4.1 1017 contributed proofs through DeepSeek Harness. Codex supervised the campaign and contributed dependency analysis and proof edits. Each core’s verification file identifies its contributions. Keith Adler’s published dependency-pruning analysis informed the search.

Fortytwo removed the unused archimedean sign subgroup, character and finite-index construction from HeckeCharRayClass. Codex specialized the finite Fourier transform to the unramified lattice, the archimedean product to real places, and the identity theorem to the actual finite pole set. The mathematical formalization is by Levent Alpöge. Codex chose the integral finite-adèle lattice indicator as the unramified test function and used its known Fourier transform. The weights vanish for class-group characters, so Codex used only the even real Gaussian for the archimedean Fourier and Mellin integrals. Codex extended the unramified normalized L-function at zero by its punctured-neighborhood limit. Codex proved triviality on each archimedean local group and computed its radial Gaussian integral directly, eliminating the classification of general real and complex unit characters. The character is trivial on the modulus section, so Codex used an unshifted Mellin transform and continued the functional equation away from the two possible poles, zero and one. Codex used the nonzero residue of the Dedekind zeta function to obtain absolute convergence further to the right, replacing the ideal-count growth argument. Codex expressed the L-series as an absolutely convergent sum over integral ideals. Codex proved that any idele above a nonzero ideal gives the same coefficient, since the character is trivial on the kernel of the fractional ideal map.

Levent Alpöge authored the original Core 37 formalization. Codex reduced the Bernstein–Zelevinsky finite-length proof by narrowing dependencies in two modules. Fortytwo conducted the preceding search and verified the parent proof. Its edit to ExampleSatisfiesConditionsAtFive falls outside this 74-file import closure. The independent local Comparator and Lean default kernel accepted this source-only study.

Core 40. Fortytwo’s native DeepSeek session supplied the entrywise diagonal and unipotent coordinate arguments in the published Fortytwo lineage. Mikko Nyman and collaborators shortened the torus and Haar arguments in #103701 and explicitly credit Fortytwo #103322. Codex applied the equality of the complete mapped matrix. For a second fundamental domain the proof now uses absolute continuity of additive Haar measures directly. The positive Haar scalar is used only to provide the nonzero proportionality factor. The unchanged target and formalization are by Levent Alpöge. The Borel identification for adelic block coordinates is applied directly to the constant-term equation. [Published starting proof](https://riemann.verifytask.cn/api/attempt/103701)

For Core 41, Codex narrowed the imports in Levent Alpöge’s `DiscreteSeriesWeylDimension.lean`. The same change was verified in the joint Core 25 proof. Fortytwo DeepSeek contributed to the earlier Core 25 search.

| Core | Editable Lean files | Baseline tokens | Verified local tokens | Tokens saved |
| ---: | ---: | ---: | ---: | ---: |
| 14 | 1,102 | 3,467,872 | 1,589,269 | 1,878,603 |
| 15 | 28,473 | 60,808,488 | 47,870,200 | 12,938,288 |
| 17 | 30,501 | 48,886,000 | 48,885,898 | 102 |
| 18 | 33,702 | 75,331,745 | 74,343,508 | 988,237 |
| 20 | 12,327 | 24,561,483 | 20,122,016 | 4,439,467 |
| 22 | 20,228 | 38,808,445 | 38,806,732 | 1,713 |
| 23 | 8,266 | 47,617,266 | 19,763,509 | 27,853,757 |
| 24 | 12,931 | 30,828,159 | 26,514,268 | 4,313,891 |
| 25 | 4,150 | 29,435,752 | 6,954,104 | 22,481,648 |
| 26 | 242 | 540,118 | 366,542 | 173,576 |
| 28 | 146 | 920,317 | 255,800 | 664,517 |
| 29 | 59 | 831,319 | 89,033 | 742,286 |
| 30 | 340 | 1,438,064 | 840,988 | 597,076 |
| 31 | 277 | 420,267 | 282,489 | 137,778 |
| 32 | 370 | 607,551 | 554,450 | 53,101 |
| 33 | 42 | 826,075 | 69,093 | 756,982 |
| 34 | 127 | 400,204 | 105,279 | 294,925 |
| 35 | 185 | 773,767 | 328,750 | 445,017 |
| 36 | 1 | 1,023,975 | 230 | 1,023,745 |
| 37 | 74 | 1,852,115 | 256,560 | 1,595,555 |
| 40 | 1 | 1,031,987 | 371 | 1,031,616 |
| 41 | 970 | 3,282,020 | 2,955,155 | 326,865 |

The independent Comparator and the Lean 4.33.1 default kernel accepted each exact target with `propext`, `Quot.sound` and `Classical.choice`. Each directory records the local replay, complete source-tree digest, Mathlib revision and the checksums of its original sources. The local check derived the protected boundary from the organizer’s published frozen roots. The table reports locally measured token counts.

## Reproduce the proof sources

Download the `coreN.tar.zst` archive linked in the core’s `verification.json`. From this directory, run the command with Python 3.14 and Git installed. Choose a new output directory.

```sh
python3.14 reconstruct.py 24 /path/to/core24.tar.zst /tmp/fortytwo-core24/proof
```

The script checks the archive, applies the Lean edits, follows imports within the editable shard and verifies the resulting source tree. Use the reconstructed `proof/` directory in the core’s pinned Lean challenge environment.
Fast cores record their upstream Git revision and per-file SHA-256 values in `verification.json`. Pass the upstream checkout’s `src` directory as the second argument, for example `python3.14 reconstruct.py 26 /path/to/riemann-lean/src /tmp/core26-proof`.

[Organizer source shards](https://github.com/Osgood001/riemann-hypothesis/releases/tag/v2026.11.23-shards)

Core 14 uses the pinned upstream checkout recorded in its verification file. Run `python3.14 reconstruct.py 14 /path/to/riemann-lean/lean/src /tmp/core14-proof` from this directory.
