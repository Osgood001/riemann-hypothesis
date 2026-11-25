# Core 19: one coefficient-field witness per key pair

The same pair of transport keys can be used in many compatible stages.
For a fixed pair, choose one algebraic number that generates the compositum
of the two fields used in the original transport proof. A stage whose embedded
field contains that number contains both fields. The new
exGrid_for_key_pair_of theorem assumes neither KeyFin nor GKeyFin; those
hypotheses are only needed to collect the certificates for the original
exGrid_of, whose statement is unchanged.

This is a staged alternate proof. It does not modify src/ in this PR and
does not claim a leaderboard result. It is based on Levent Alpöge's
GridExistenceOfPieces proof. PR #53 instead encodes the full set of
certificates in a single number after considering all key pairs.

## Reproduce

At the organizer's base commit 535c9103a305e822d2adb1830981ec4dd0916621,
using the pinned Lean 4.36.0 dependencies and cache, place the enclosed file at
src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GridExistenceOfPieces.lean
and compile that module. No imports change. Compare the exGrid_of type to the
base file. Both exGrid_for_key_pair_of and exGrid_of were checked with warnings
as errors and use only propext, Classical.choice, and Quot.sound. Independent
con-ron in verified mode replayed the two declarations together: 88,308
reachable declarations accepted. This does not claim a rebuild of existing
callers against the proposed replacement.
