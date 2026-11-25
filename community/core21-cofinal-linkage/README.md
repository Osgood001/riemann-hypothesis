# Core 21: definite-side assembly from cofinal linkage

The original assembly takes a linkage witness at every real parameter. The proof
only needs one witness above the two thresholds for the evaluation grid and the
row functional. The new theorem
`AlpogeRHCore21.nonemptyHypsDefiniteSideOfClosedBoundCofinal` assumes
`∀ lower, ∃ cDep, lower ≤ cDep ∧ LinkedAt …` instead. Select a witness above the
maximum of the two thresholds and use that same parameter throughout. The
unchanged challenge statement follows by taking `cDep = lower` when linkage
holds everywhere.

The standalone package does not need the original module's second theorem,
`every_character_of_theta_integrals_local_matching`. Excluding that consumer
allows the `FockModels.EveryCharacterE`, `TopPlug`, and `At23OfAll` imports to be
omitted; the row-rationality lemma is imported directly. The underlying
formalization is Levent Alpöge's. Vilin97's earlier
[maintained-tree import minimization](https://github.com/leanprover-community/riemann-hypothesis/commit/e2d63d253904023ae299743da96a19ea8cd73fce)
already narrowed the `EveryCharacterE` dependency while retaining the second
theorem. This package targets only the original Core 21 challenge, not
maintained `src/`.

## Reproduce

Download `core21.tar.zst` from the
[organizer's source shards](https://github.com/Osgood001/riemann-hypothesis/releases/tag/v2026.11.23-shards).
Verify SHA-256 `341ffc5b27d47dc6312257cd02b01fccdd5f99dd16bce625d56f8cb4cd2f0836`
and extract it. Then run:

```sh
python3 materialize.py path/to/extracted-shard path/to/new/proof
```

This reconstructs the counted Lean sources and checks the path-and-content digest.
The organizer's frozen dependencies are not included. For local elaboration use
Lean `4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and the
matching original dependency outputs. The
[published challenge](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-21-nonempty-def-7c453180)
supplies the target statement and frozen roots.

## Comparison

The complete reconstructed submission has **38,995 Lean files and 61,883,858
normalized tokens**, including both the exact target and the stronger theorem.
The published original baseline is **61,172 files and 94,839,307 tokens**.
That is **32,955,449 fewer tokens (34.75%)**. Both counts include the entry
point and exclude frozen files. This is a comparison with Alpöge's published
baseline, not a hosted score or a claim about ungraded submissions. Some
[ungraded attempts](https://play.bohrium.com/api/challenges/lean-4-verification-rh-core-pillar-21-nonempty-def-7c453180/attempts?limit=100)
report similar or smaller file counts but no verified token counts. The cofinal
theorem is the substantive change.

`verification.json` records the pinned sources and local checks.

## Verification

Lean 4.33.1 elaborated the package entry point with warnings as errors and
accepted the resulting proof at the verbatim published challenge type. Both
the original and cofinal statements use only the three standard axioms.
Independent con-ron replay selected both declarations from the exact compiled
module and accepted 932,346 reachable declarations in verified mode. The
separate export-based Comparator did not produce a verdict.
