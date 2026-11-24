# Fortytwo Phase 3 proof reductions

These source changes reduce the size of Levent Alpöge’s Phase 3 proofs. Fortytwo Engine: Deepseek Flash V4.1 1017 contributed proofs through DeepSeek Harness. Codex supervised the campaign and contributed dependency analysis and proof edits. Each core’s verification file identifies its contributions. Keith Adler’s published dependency-pruning analysis informed the search.

Fortytwo removed the unused archimedean sign subgroup, character and finite-index construction from HeckeCharRayClass. Codex specialized the finite Fourier transform to the unramified lattice, the archimedean product to real places, and the identity theorem to the actual finite pole set. The mathematical formalization is by Levent Alpöge. Codex chose the integral finite-adèle lattice indicator as the unramified test function and used its known Fourier transform. The weights vanish for class-group characters, so Codex used only the even real Gaussian for the archimedean Fourier and Mellin integrals. Codex extended the unramified normalized L-function at zero by its punctured-neighborhood limit. Codex proved triviality on each archimedean local group and computed its radial Gaussian integral directly, eliminating the classification of general real and complex unit characters. The character is trivial on the modulus section, so Codex used an unshifted Mellin transform and continued the functional equation away from the two possible poles, zero and one. Codex expressed the L-series as an absolutely convergent sum over integral ideals. Codex proved that any idele above a nonzero ideal gives the same coefficient, since the character is trivial on the kernel of the fractional ideal map.

Levent Alpöge authored the original Core 37 formalization. Codex reduced the Bernstein–Zelevinsky finite-length proof by narrowing dependencies in two modules. Fortytwo conducted the preceding search and verified the parent proof. Its edit to ExampleSatisfiesConditionsAtFive falls outside this 74-file import closure. The independent local Comparator and Lean default kernel accepted this source-only study.

Core 40. Fortytwo’s native DeepSeek session supplied the entrywise diagonal and unipotent coordinate arguments in the published Fortytwo lineage. Mikko Nyman and collaborators explicitly credit Fortytwo #103322 in their #103701 and shortened the torus, Haar measure and unipotent arguments. Starting with that published file, Codex used the equality of the complete mapped matrix before taking entries and reused the Haar scalar nonzero witness. The unchanged target and formalization are by Levent Alpöge. [Published starting proof](https://riemann.verifytask.cn/api/attempt/103701)

For Core 41, Codex narrowed the imports in Levent Alpöge’s `DiscreteSeriesWeylDimension.lean`. The same change was verified in the joint Core 25 proof. Fortytwo DeepSeek contributed to the earlier Core 25 search.

| Core | Editable Lean files | Baseline tokens | Verified local tokens | Tokens saved |
| ---: | ---: | ---: | ---: | ---: |
| 14 | 1,121 | 3,467,872 | 2,150,099 | 1,317,773 |
| 15 | 28,473 | 60,808,488 | 47,870,200 | 12,938,288 |
| 17 | 30,501 | 48,886,000 | 48,885,898 | 102 |
| 18 | 33,702 | 75,331,745 | 74,343,508 | 988,237 |
| 22 | 20,228 | 38,808,445 | 38,806,732 | 1,713 |
| 23 | 8,266 | 47,617,266 | 19,763,509 | 27,853,757 |
| 24 | 12,931 | 30,828,159 | 26,514,268 | 4,313,891 |
| 25 | 4,382 | 29,435,752 | 7,851,988 | 21,583,764 |
| 26 | 242 | 540,118 | 366,542 | 173,576 |
| 28 | 151 | 920,317 | 260,150 | 660,167 |
| 29 | 59 | 831,319 | 89,268 | 742,051 |
| 30 | 372 | 1,438,064 | 1,188,387 | 249,677 |
| 31 | 282 | 420,267 | 286,968 | 133,299 |
| 32 | 372 | 607,551 | 555,796 | 51,755 |
| 33 | 42 | 826,075 | 69,093 | 756,982 |
| 34 | 127 | 400,204 | 105,279 | 294,925 |
| 36 | 1 | 1,023,975 | 682 | 1,023,293 |
| 37 | 74 | 1,852,115 | 256,560 | 1,595,555 |
| 40 | 1 | 1,031,987 | 558 | 1,031,429 |
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
