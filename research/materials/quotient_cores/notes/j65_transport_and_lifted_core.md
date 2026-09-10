# transported J65 cuts and lifted proof-core experiment

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Context

analysis converted the saved analysis complete-Wang LP point into a replayable integer consequence.  Let `J` be the 65 nonzero E11 quotient directions of that LP point.  The verified CNF/DRAT proof for the J-face says that no distinct 19-point E11 A-support contained in `J` satisfies all 417,199 complete E11 Wang occupation rows.  Equivalently, every complete-Wang distinct support must have at least one point outside `J`, or `sum_{p in J} x_p <= 18`.

The purpose of analysis was to make that consequence more reusable and to understand whether the proof was really tied to all 190 directions outside `J`.

## 1. Transported orbit of the J65 cut

Script: [transport_j65_family_lp.py](../code/transport_j65_family_lp.py).

Output files:

- [transported_J65_family.json](../results/j65_transport/transported_J65_family.json)
- [lp_with_transported_J65_cuts.json](../results/j65_transport/lp_with_transported_J65_cuts.json)

Using the same E11 stabilizer permutations whose complete-Wang invariance was verified in analysis, the 65-set `J` has 1,152 distinct whole-set images.  Thus each image `gJ` gives a valid transported cut

```text
sum_{p in gJ} x_p <= 18.
```

No new proof is needed for these images because the original J65 proof is transported by a whole stabilizer element preserving the E11 Wang table.

Recorded summary:

- unique images: 1,152
- image family SHA256: `d4b97321687ecfe856295cc6fdaa52758d28b246de0cd14387e2dbba85b07ebd`
- every image has size 65
- point-frequency histogram across the 1,152 images:
  - 96 points occur in 264 images
  - 72 points occur in 288 images
  - 36 points occur in 320 images
  - 36 points occur in 352 images
  - 6 points occur in 768 images
- overlap with the original `J` ranges from 10 to 65; many images overlap the original strongly, so the family is not simply 1,152 independent exclusions.

The complete Wang LP with all 1,152 transported cuts remains fractional.  Three tested objectives:

1. maximize old `J` mass: feasible LP with mass on old `J` equal to 18, 68 nonzero fractional coordinates, and exactly one transported cut tight;
2. random seed 630631: feasible LP with 71 fractional nonzero coordinates, max transported-J mass about 9.6753, no transported cut tight;
3. random seed 630632: feasible LP with 65 fractional nonzero coordinates, max transported-J mass about 8.5518, no transported cut tight.

Thus the transported family removes the old face and its orbit, but random LP optima can avoid the entire family with large slack.

## 2. Extracting the DRAT input core and mapping it to Wang rows

A background run executed

```text
drat-trim workspace/data/global_J_face/cnf/J65_complete_wang.cnf \
  workspace/data/global_J_face/cnf/J65_complete_wang.drat \
  -c workspace/data/jface_core/J65_input_core.cnf
```

and returned `VERIFIED`.  The extracted core contains 38,800 input clauses.

Script: [analyze_j65_input_core.py](../code/analyze_j65_input_core.py).

Output files:

- [J65_core_clause_analysis.json](../results/jface_core/J65_core_clause_analysis.json)
- `workspace/data/jface_core/J65_core_used_constraints.pkl`
- `workspace/data/jface_core/J65_core_used_constraints.jsonl`

The regenerated analysis J-face clause stream matched the extracted core exactly: 38,800/38,800 core clauses matched, with zero unmatched clauses.

Breakdown:

- exact-size-19 clauses in core: 1,079
- row-encoding clauses in core: 37,721
- restricted Wang constraints contributing at least one core input clause: 9,469
- representative full-row dimensions among those constraints:
  - dim 2: 138
  - dim 3: 5,069
  - dim 4: 1,060
  - dim 5: 1,833
  - dim 6: 1,265
  - dim 7: 104
- representative full-row L-values among those constraints:
  - L=3: 12
  - L=6: 95
  - L=9: 405
  - L=11: 2
  - L=12: 1,144
  - L=13: 113
  - L=14: 669
  - L=15: 1,379
  - L=16: 1,333
  - L=17: 4,299
  - L=18: 18

These 9,469 rows are not a replacement for the full 417,199-row table.  They are a concrete row subset extracted from the proof of the old J-face exclusion, useful for studying which escape directions interact with that proof.

## 3. Lifting the proof-core rows to full 255-point incidence

Script: [lift_jcore_assumption_min.py](../code/lift_jcore_assumption_min.py).

Output files:

- `workspace/data/lifted_jcore/lifted_used_rows_all190_units.cnf`
- `workspace/data/lifted_jcore/lifted_used_rows_all190_units.drat`
- [lifted_used_rows_all190_units.status.json](../results/lifted_jcore/lifted_used_rows_all190_units.status.json)
- [lifted_used_rows_all190_units.meta.json](../results/lifted_jcore/lifted_used_rows_all190_units.meta.json)
- `workspace/data/lifted_jcore/lifted_used_rows_all190_units.input_core.cnf`
- [lifted_used_rows_all190_units_core_units.json](../results/lifted_jcore/lifted_used_rows_all190_units_core_units.json)

This formula uses:

- 255 primary variables;
- exact cardinality 19;
- the 9,469 representative full E11 Wang rows extracted above;
- unit assumptions `x_p=0` for all 190 points outside `J`.

CaDiCaL returned UNSAT and `drat-trim` returned VERIFIED.  Hashes from the status file:

- CNF SHA256: `c7d8a0de94bde4d15215d80e0f2cb79ebaa1b7f7a9a3ab75e117a15bd8950468`
- DRAT SHA256: `db5207ace2a83a1ec4e686d1b9224a07da72f73377151f4306b1a3bb7d751e05`
- extracted input-core SHA256: `8a244355bf8d913fe0251a5997a1e9d8234c9d1ff6187372de8915cc34ab0bfb`

The lifted all-unit input core still used all 190 outside negative unit clauses.  Therefore this direct proof-core extraction did not yield a smaller subset `K` with `sum_{p in K} x_p >= 1`.  This does not prove no smaller `K` exists; it only says the proof and core produced by this solver/encoding retained every outside-zero assumption.

## 4. Budgeted escape experiments for the lifted proof-core rows

Script: [lifted_core_escape_analysis.py](../code/lifted_core_escape_analysis.py) and sweep script [lifted_core_outside_sweep.py](../code/lifted_core_outside_sweep.py).

Output files:

- [lifted_core_escape_analysis.json](../results/lifted_jcore/lifted_core_escape_analysis.json)
- [lifted_core_outside_sweep.json](../results/lifted_jcore/lifted_core_outside_sweep.json)

With only the 9,469 lifted proof-core Wang rows and no outside-zero units, CP-SAT found supports satisfying these 9,469 rows after selecting outside points, but those supports still violate the full Wang table.

Important observed facts:

- `max_outside <= 0`: CP-SAT INFEASIBLE for the lifted proof-core rows.
- `max_outside <= 1`: CP-SAT INFEASIBLE for the lifted proof-core rows.
- `max_outside <= 2`: CP-SAT INFEASIBLE for the lifted proof-core rows in the 60s sweep.
- `max_outside <= 3` and `<=4`: UNKNOWN in the short sweep.
- `max_outside <= 5`: CP-SAT found a support with five outside points; rescanning it against all 417,199 rows found 25 complete-Wang violations.
- A separate minimize-outside run found a support with five outside points and 35 complete-Wang violations, but the CP-SAT status was FEASIBLE after timeout, not an optimality proof.

The lifted proof-core rows therefore appear to require at least several escape directions, but this is not yet a replayable mathematical consequence except for the all-190-unit J-face proof above.  A CNF trying to prove the stronger consequence for `max_outside <= 1` was built by [lifted_core_outside_cnf.py](../code/lifted_core_outside_cnf.py):

- CNF: `workspace/data/lifted_jcore/cnf/lifted_core_outside_le_1.cnf`
- CNF SHA256: `15a233f43e5d0d6cd6ff3462ffb94d90ab354d6761f362f3116bba5845df8ec0`
- CaDiCaL ran 900 seconds and returned UNKNOWN; no DRAT verification exists for this stronger consequence.

## 5. New LP faces from transported-cut LP runs

Script: [general_face_cpsat.py](../code/general_face_cpsat.py).

Output files:

- [face_cpsat_transJ65_random630631.json](../results/face_loop/face_cpsat_transJ65_random630631.json)
- [face_cpsat_transJ65_random630632.json](../results/face_loop/face_cpsat_transJ65_random630632.json)

The two random LP optima after adding all transported J65 cuts gave positive supports of sizes 71 and 65.  Complete-Wang CP-SAT face tests returned INFEASIBLE quickly:

- random seed 630631 support face: size 71, CP-SAT INFEASIBLE in 29.640s;
- random seed 630632 support face: size 65, CP-SAT INFEASIBLE in 20.039s.

These are promising new fractional faces for replayable CNF/DRAT proofs, but the current status is CP-SAT evidence only.  If replayed, each would add another valid face cut `sum_{p in J_i} x_p <= |J_i|-1`?  For this support-size/19 problem the exact consequence is no 19-support contained in `J_i`, so the cut is `sum_{p in J_i} x_p <= 18`, regardless of `|J_i|`.

## 6. Complete-table escape tests near original J

Script: [j_escape_cpsat.py](../code/j_escape_cpsat.py).

Output files:

- [complete_wang_max_outside_1_180s.json](../results/j_escape/complete_wang_max_outside_1_180s.json)
- [complete_wang_max_outside_2_180s.json](../results/j_escape/complete_wang_max_outside_2_180s.json)

These models used the complete 417,199-row Wang table and constrained the selected support to have at most one or two points outside the original analysis `J`.

Both runs returned UNKNOWN within the 180-second budget.  Therefore the complete Wang table has not yet been shown to force two or three outside points from the original J-face, and no support in these regimes was found.

## 7. related analysis update kept separate

related analysis record reports a characteristic-zero transpose-layer update: the anti-sector complementary lower bound becomes `m0 >= 7` from an exact A-wedge flattening of rank 27 over characteristic not 2, with each structured tau-free orbit contributing image rank at most 4.  This removes standard tau rank-22 skeletons `(12,5)` and `(10,6)`, while `(8,7)`, `(6,8)`, `(4,9)`, `(2,10)`, and `(0,11)` remain.  related analysis also records that literal tau-fixedness alone is not a novelty marker because known rank-23 families can have transpose-like cyclic/sandwich symmetries.

This is useful but independent of the related analysis finite-field E11 occupation work.  It must not be merged into an `F2` lower-bound statement.

## Research meaning after analysis

The analysis J65 cut is now reusable under a 1,152-image stabilizer orbit.  The LP remains fractional after adding the whole family, so this family is not close to a complete distinct-branch exclusion by itself.

The proof-core extraction showed that the old J-face contradiction uses a much smaller row subset than the full table, but the direct lifted all-unit proof still uses every outside-zero unit.  No smaller `K` has yet been certified.  CP-SAT exploration suggests that the 9,469 lifted proof-core rows may already force at least three outside-J points, but a CNF/DRAT attempt for the weaker `outside <= 1` consequence timed out.  This points to an encoding/proof-production problem rather than a settled mathematical result.

The most useful continuation is to make the cutting-plane loop proof-producing for the new LP faces and to improve the lifted proof-core proof encoding.  A feasible complete-Wang face support would be immediately valuable as input to the fixed-A B/C completion pipeline.  An infeasible face is valuable only after CNF/DRAT or another replayable certificate turns it into a valid support cut.
