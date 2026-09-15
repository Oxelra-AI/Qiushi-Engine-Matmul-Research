# Fourteen Two-Plane Orbits

This is a separate extension of the eight-orbit deliverable `2f93acc` described
in `ORBIT_SIZES.md`. It changes neither that deliverable's Lean modules nor
the main theorem, its imports, premises, or report sources.

## Statements

The namespace `QiushiMatmul.PlaneOrbit.FullClassification` indexes the existing
`frozenWangBasis` entries 478--491 by `Fin 14`. In this order, `sizes` is:

```
98, 441, 882, 3528, 1764, 4704,
98, 2352, 1176, 3528, 14112, 4704, 4704, 1344
```

`QiushiPlaneOrbitClassification` proves individual orbit sizes, representative
dimension two, pairwise inequivalence, unique classification of every actual
two-dimensional submodule, and exactly fourteen quotient classes. Its relation
is the same full invertible-action/transpose `Equivalent` as the first eight.

`QiushiPlaneOrbitNormalForm` proves `PlaneOrbit.equivalent_iff_transport`,
connecting that equivalence to one invertible matrix action with an optional
preceding transpose. The proof uses closure of matrix sandwiches `A -> L A R`
under the four generators;
the existing semantic closure theorem handles arbitrary invertible actions.
No matrix-group multiplication table or additional exhaustive classifier is
generated.

`QiushiPlaneOrbitFrozenClassification` states the result through the existing
frozen-table predicate, not a replacement orbit relation:

```lean
frozen_classification (W : Space) (hW : Module.finrank F2 W = 2) :
  ∃! i : Fin 14, frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W

frozen_orbit_sizes (i : Fin 14) :
  Nat.card {W : Space //
    frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W} = sizes i

frozen_representatives_inequivalent (i j : Fin 14) (hij : i ≠ j) :
  ¬ frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ (frozenRep j)
```

## Coverage Argument

Only six additional certificates are generated. All fourteen reuse
`OrbitData.orbit_exact`, `space_injective`, `dimension`, and
`equivalent_root_keys`. The disjoint union of their index types has cardinality
43,435 and injects into the type of actual dimension-two submodules. Applying
the existing `FullSubspaceCount.mat3_two_plane_count` makes this injection
surjective. Pairwise inequivalence gives uniqueness.

The 43,435 theorem is applied, not assumed as a new premise and not reproved.
No 32,018 all-high count or six-bases theorem is duplicated. No classification
premise is added to the main proof.

## Private Replay

Use the same pinned environment as the eight-orbit deliverable. The parent
sources `QiushiFrozenOrbitTable.lean`, `QiushiFrozenWangData.lean`, and
`QiushiMat3SubspaceCount.lean` were copied unchanged into the ignored private
directory `.local/finite-orbits/parent-src/` and compiled there. Their source
hashes and return codes are in the replay receipt. They are existing parent
dependencies, not replacement implementations in this commit.

```sh
python3 tools/generate_finite_orbits.py --remaining-six
python3 tools/build_finite_orbits.py --environment "$CLEAN_ENVIRONMENT" --jobs 2 \
  .local/finite-orbits/parent-src/*.lean \
  QiushiPlaneOrbit47[89]*.lean QiushiPlaneOrbit48[0-3]*.lean \
  QiushiPlaneOrbitClassification.lean QiushiPlaneOrbitClassificationTests.lean \
  QiushiPlaneOrbitNormalForm.lean QiushiPlaneOrbitFrozenClassification.lean
python3 -m unittest discover -s tests -p test_finite_orbits.py -v
```

On the integrated parent, use its existing copies of the three support sources
instead. No imports from any other parent object directory are needed.
The builder now retains timestamped receipts as well as `last-build.json`.

All fourteen size certificates, the finite-cardinality classification, quotient
count, direct transport normal form, and frozen-table statements passed kernel
checking on 2026-09-14. The printed dependencies of the public statements and
`equivalent_iff_transport` are exactly `propext`, `Classical.choice`, and
`Quot.sound`. No custom axiom, native decision procedure, or admitted proof is
used. Four producer/source tests also pass; those tests are diagnostics, not
proof premises.

The final receipt audit matched the current source hashes of all 384 orbit
modules and three unchanged parent dependencies to successful kernel replays
across seven receipts. Every receipt uses the same environment SHA256:
`3666edf796bb456313cef1b76a7011786ec9a0402b50be117d2dc7a1a558e904`.
