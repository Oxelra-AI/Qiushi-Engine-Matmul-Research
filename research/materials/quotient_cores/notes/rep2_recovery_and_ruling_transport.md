# Recovery from false zero-survivor claim and rep2 ruling-line continuation

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. analysis zero-survivor claim is withdrawn

The review warning was correct.  The new analysis diagnostic decoded Wang LUT keys incorrectly by reading nine-bit chunks from bit zero.  The canonical encoding, implemented in [wang_capacity_lazy.py](../../occupation_and_completion/code/wang_capacity_lazy.py), is `d = key & 0xF`, then exactly `d` nine-bit basis vectors from `key >> 4`.

The corrected diagnostic/audit is saved at:

- [corrected_decode_and_rep2_base.py](../code/corrected_decode_and_rep2_base.py)
- [corrected_decode_and_rep2_base.json](../../finite_certification/results/decode_correction/corrected_decode_and_rep2_base.json)
- [decode_correction_and_rep2_retraction.md](../../finite_certification/notes/decode_correction_and_rep2_retraction.md)

Key findings from the corrected run:

- key `0x11945003` decodes to dimension `3`, basis `[256,162,70]`, and does not contain points `1`, `2`, or `100`; the broken analysis decoder produced `[3,40,101,2]`.
- over all 8,283,458 LUT rows, canonical decoding round-trips through `rref_key(unpack_basis(key))`, and no duplicate-pivot examples occur in the canonically decoded basis list.
- prefix `[1,2]` has `0` residual-0 vertex exclusions and `509` survivors, not zero survivors.
- prefix `[1,2,3]` has `372` residual-0 vertex exclusions and `136` survivors, agreeing with the earlier analysis/analysis marked-prefix base graph.

## 2. What remains valid from analysis

The local fixed-prefix proof for `[1,2,3]` remains valid:

- [strict_verification.json](../results/rep2_rep003_promotion/lowres_12w8/strict_verification.json)
- review reading: `independent-verification-record`

Interpreted carefully, this excludes 20 distinct projective A-point Wang supports containing `[1,2,3]`, conditional on the Wang LUT, branch normalization, and encoding semantics.  It does **not** close rep2.

The ruling-line transport is the right way to reuse this result: the excluded rank-1 line `{1,2,3}` transports to all 98 Segre ruling-line triples.  For the rep2 prefix `[1,2]`, these simplify to 1 unit (`3`), 10 binary clauses, and 87 ternary clauses.  They are derived constraints with separate proof provenance, not primitive Wang rows.

## 3. Ruling-line clauses tested as a rep2 augmentation

I built:

- [rep2_ruling_augmented.py](../code/rep2_ruling_augmented.py)

It revalidates an existing rep2 `learned_clauses.jsonl` seed, adds the transported ruling-line clauses, solves the augmented formula, and scans SAT models against the full LUT.

Results:

- [summary.json](../results/rep2_ruling_augmented/seed12/summary.json): 9,903 learned clauses from the 12-round seed plus 95 new ruling clauses (3 duplicates already present) gives 56,630 clauses; CaDiCaL is SAT immediately; returned support has 12,625 full-LUT violations.
- [summary.json](../results/rep2_ruling_augmented/prod120/summary.json): 207,408 learned clauses from the analysis 120-round production seed plus 95 new ruling clauses gives 254,135 clauses; CaDiCaL is SAT immediately; returned support has 4,054 full-LUT violations.

Thus ruling-line transport as a static add-on does not close rep2, but it is still a valid structural constraint that can shape later branching/search.

A managed continuation was started:

- task `s38_t34_tool1`
- output target `workspace/data/rep2_ruling_witness_continue/prod120_ruling/`
- script [rep2_ruling_witness_continue.py](../code/rep2_ruling_witness_continue.py)
- purpose: continue model-driven witness separation for up to 8 rounds from the strongest 120-round seed, with ruling-line clauses present from the start.

Do not infer the result until the runtime delivers the task output.

## 4. Rank-1 projection consequences for rep2

I profiled the rank-1 part under the transported ruling-line clauses and under the full rank-1 projection of Wang occupation:

- [rep2_rank1_ruling_profile.py](../../occupation_and_completion/code/rep2_rank1_ruling_profile.py)
- [summary.json](../../occupation_and_completion/results/rep2_rank1_ruling_profile/summary.json)
- [rank1_projection_with_pair.py](../../occupation_and_completion/code/rank1_projection_with_pair.py)
- [no_ruling_max.json](../../occupation_and_completion/results/rank1_projection_pair/no_ruling_max.json)
- [with_ruling_max.json](../../occupation_and_completion/results/rank1_projection_pair/with_ruling_max.json)

Findings:

- Ruling-line triples alone allow 26 additional rank-1 candidates, i.e. 28 rank-1 points total including `[1,2]`.
- The rep2 residual-0/1 Wang base graph has no edges or units among rank-1 candidate variables, so it does not constrain the rank-1 subset directly.
- The full 49-variable rank-1 projection of the Wang LUT with fixed adjacent pair `[1,2]` has CP-SAT optimum 18 rank-1 points total.
- Adding the 98 transported ruling-line constraints does **not** lower that optimum; optimum remains 18.

Interpretation: in the rep2 branch, any 20-point Wang-admissible support can have at most 18 rank-1 A-points under the projected necessary system, so it must contain at least two higher-rank points. This is useful route-shaping evidence and agrees with the older exact-rank-1 count closure, but it is not a full adjacent-pair branch proof.

## 5. Current finite-field state after analysis

- Matching branch: 15/38 strata closed (unchanged from analysis).
- Rep2 adjacent-pair branch: open.
- Valid local rep2 marked-prefix closure: `[1,2,3]` only.
- Valid transported constraints: all 98 rank-1 ruling-line triples are forbidden as derived consequences of the `[1,2,3]` proof plus group equivariance, but they do not close rep2 when added naively to existing formulas.
- No proof of `R_F2(T_<3,3,3>) >= 21` yet.

The best next finite-field work is to continue proof-producing rep2 search with the ruling-line constraints and to develop a stronger decomposition around rank-1 count/high-rank pair structure, not to revive the withdrawn zero-survivor route.
