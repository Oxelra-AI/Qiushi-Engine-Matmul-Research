# Selected Frozen-Wang Numeric Bindings

Import `QiushiFrozenWangBindings` for all eight planes, or
`QiushiFrozenWangPlane484` through `QiushiFrozenWangPlane491` individually.

All binding declarations are in `QiushiMatmul.FrozenWang`. The concrete table
remains `QiushiMatmul.frozenWangTable`, defined by `QiushiFrozenWangData`.

## Public Interface

For each literal `N` from 484 through 491, the module supplies:

```lean
theorem planeN_source : ∀ i : Fin planeNGenConfig.nOcc,
  planeNGenConfig.sourceLb i ≤
    frozenWangTable.L0 (planeNGenConfig.sourceU i)

theorem planeN_dead : ∀ d : Fin planeNGenConfig.nDead,
  planeNGenConfig.target ≤
    frozenWangTable.L0 (planeNGenConfig.deadU d)
```

Here `N` is a documentation placeholder, not a new config selector. For example,
the first theorem is `QiushiMatmul.FrozenWang.plane484_source`. None of these
theorems has a table-soundness, source-rank, orbit-classification, or transport
hypothesis.

| Plane | Source Rows | Dead Rows | Total |
| --- | ---: | ---: | ---: |
| 484 | 1665 | 84 | 1749 |
| 485 | 421 | 86 | 507 |
| 486 | 262 | 86 | 348 |
| 487 | 668 | 79 | 747 |
| 488 | 413 | 86 | 499 |
| 489 | 371 | 95 | 466 |
| 490 | 713 | 84 | 797 |
| 491 | 726 | 78 | 804 |
| Total | 5239 | 678 | 5917 |

All actual spaces have dimension 3 through 8. The 5917 rows share 4543 distinct
bases from 122 representative orbits; 824 distinct-space transports use the
transpose choice.

## Proof Dependencies

`QiushiFrozenWangChecks` proves selected-index basis/label values and concrete
matrix determinant/inverse facts by kernel computation. These are proved facts
about definitions, not assumed table lemmas.

Each `spaceNNNN_orbit` proves exact `frozenWangTable.OrbitImage` membership
using `frozenOrbitImage_of_code_transport`. Pairs name actual target generators
and their source preimages. Lean checks forward membership, their matrix
images, and reverse coverage of every frozen source generator by the preimage
span. Each `spaceNNNN_lower` follows from `FrozenOrbitTable.lower_le_L0`.

Each concrete source/dead row then checks the selected entry of the existing
`planeNGenConfig` arrays. The final universal theorems assemble all finite
blocks using `forall_fin_of_blocks`, including partial last blocks. The
noncomputable L0 supremum is never unfolded at a concrete table.

`QiushiFrozenWangAudit` prints the transitive axioms and exact types of all
sixteen universal source/dead theorems. The build driver accepts the audit only
when each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

Use the existing `tools/generate_frozen_table.py` to obtain
`representatives.json` and `QiushiFrozenWangData.lean` from the public protobuf.
The binding generator consumes those files and the eight existing
`certificates/N/tables.json` files. Its witness search reuses
`generate_certificate.find_transports`, `actions`, `rref`, and `span`.

Here `P` is the input formalization directory, `FROZEN` holds the two generated
frozen-data files, `PRIVATE` is an isolated worktree containing the generic
`QiushiFrozenOrbitTable.lean` API, and `CLEAN_BUILD` is the chosen clean parent
build with `environment.json` and `lib/`.

```bash
PYTHONDONTWRITEBYTECODE=1 python tools/generate_frozen_bindings.py \
  --project "$P" --frozen-dir "$FROZEN" \
  --out "$PRIVATE/formalization" \
  --work-dir "$PRIVATE/.local/frozen-bindings"

python tools/build_frozen_bindings.py \
  --source "$PRIVATE/formalization" \
  --manifest "$PRIVATE/.local/frozen-bindings/manifest.json" \
  --core-build "$CLEAN_BUILD" \
  --out "$PRIVATE/.local/frozen-build" --jobs 4
```

The build driver replaces `LEAN_PATH` with private output followed by the
explicit clean-core/package paths recorded by the parent build. Each compiler
uses `-j1`; `--jobs` is restricted to 1 through 4. Cache receipts bind source
content, dependency fingerprints, compiler/path identity, and compiled-object
hashes. No parent source or shared compiled output is written. The generator
and build driver save input hashes, witnesses, module hashes, compiler logs,
and the final summary in the private work directory.

Run `python tools/test_generate_frozen_bindings.py -v` for the five witness-cache
validation tests. Generated block proofs currently emit an unused-simp linter
warning for `Fin.val_mk`; this is not a proof error or an additional axiom.

## Boundary

These theorems establish lower bounds on the mathematically defined frozen
orbit expansion for the selected actual rows. They do not prove equality with
the historical pickle, all-orbit classification, or every representative's
quotient-rank bound. `QiushiFullOccupation.lean` combines them with the proved
strict/proper superspace facts and logical bridge to obtain the eight full
occupation no-model results. External selected-row agreement with the released
LUT is not promoted to a Lean theorem here.
