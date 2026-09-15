# Report-to-Proof Coverage

Checked against the English report. All six report-level replay
groups passed on the source-matched build. Declaration names below are in
`QiushiMatmul`; the table records each statement's precise hypotheses and scope.

| Mathematical claim | Lean declaration | Status and scope |
| --- | --- | --- |
| Coordinate identities are actual matrix multiplication | `tensorEntry_identity_iff_bilinearAlgorithm`, `rankAtLeast_iff_bilinearAlgorithm` | Compiled in both directions for all input matrices, not an input sample |
| Concrete rank-23 upper bound | `rank23_entry_identity`, `rank_at_most_23` | Compiled; all 729 tensor coordinates checked in Lean |
| Rank-23 algorithm on all inputs | `rank23_bilinear_algorithm`, `rank23_mul_eq` | Compiled; the output coefficient has the convention-correct orientation |
| Full rank-21 lower bound | `rank_ge_21`, `provedFinitePremises` | Clean build and exact-interface checks passed; all finite premises proved, no finite-bound hypotheses remain |
| Lower bound for ordinary bilinear algorithms | `bilinear_mul_requires_21` | Compiled for every input matrix over `ZMod 2`; no assumed quotient bounds |
| Split rank sum at least 27 in each factor | `TailCoverage.all_slot_split_bounds` | Compiled for every exact decomposition |
| Convention-correct cyclic symmetry | `cycleEntryDecomp_thrice` | Compiled; the action is `(A,B,C) -> (B,C.transpose,A.transpose)` |
| Full three-parameter tensor symmetry and coefficient pullback | `FullTrilinearSymmetry.trilinear_action`, `FullTrilinearSymmetry.input_trilinear_action`, `FullTrilinearSymmetry.coefficient_pairing_pullback` | Parent compilation and seven exact-type/axiom guards passed; arbitrary invertible U, V, H, with the actual coordinate pairing and tensor contraction |
| Saturation and cross-factor product identity | `split_flattening_saturation_identities_from_A_rank`, `product_formula` | Compiled with the stated rank-sum and nonzero-factor hypotheses |
| General rank-additive matrix saturation | `GeneralSaturation.rank_additive_saturation`, `GeneralSaturation.complete_orthogonal_idempotents` | Compiled for every field, finite square dimension, finite summand index and invertible P; tests include empty dimensions, empty indices and zero summands |
| Zero-excess length-22 profiles | `length22_zero_A_excess_profiles`, `TailCoverage.length22_B_profiles`, `TailCoverage.length22_C_profiles` | Compiled for nonzero factors and rank sum 27 in the selected slot; profiles are `(17,5,0)` or `(18,3,1)` |
| Length-21 occupation caps | `length21_named_line_cap`, `length21_named_plane_cap`, `length21_affine_hyperplane_cap` | Compiled; caps are 2, 2 and 4; `provedFinitePremises` supplies the shared premise argument |
| Arbitrary nonzero line and high-pair plane caps | `TailCoverage.length21_all_line_cap`, `TailCoverage.length21_all_high_pair_plane_cap` | Compiled; instantiate with `provedFinitePremises` |
| E11 quotient decomposition lifts by three terms | `TailCoverage.e11_quotient_lifts_by_three` | Compiled for the actual quotient by `spanCodes [1]` |
| E11 rank-19 witness yields full rank at most 22 | `TailCoverage.e11_quotient_rank19_gives_full_rank22` | Compiled implication; does not assert that the core witness exists |
| Actual E11 quotient dimension and number of directions | `TailE11Scope.e11_quotient_finrank`, `TailE11Scope.e11_direction_count` | Compiled: dimension 8 and 255 projective directions, using the actual quotient space |
| E11 subspace count and exhaustive indexing | `E11SubspaceCount.e11_all_subspace_count`, `E11SubspaceCount.e11_occupation_index_complete` | Compiled: 417,199 actual subspaces including zero and the whole space; 417,197 nonzero proper subspaces |
| Saturation with zero summands allowed | `TailPadded.zero_A_excess_saturation` | Compiled without nonzero-factor hypotheses |
| At most one invertible factor at zero excess | `TailPadded.zero_A_excess_at_most_one_invertible` and its B/C versions | Compiled for arbitrary lengths and zero summands |
| Length-22 profiles without nonzero B/C assumptions | `TailPadded.length22_A_profiles_of_nonzero_A` and its B/C versions | Compiled; only nonzero factors in the selected slot are required |
| Padded length-22 alternatives | `TailPadded.length22_A_profiles_or_zero_excess_length21` | Compiled: either the two profiles hold or a zero-excess length-21 decomposition exists |
| Interval 21 through 23 | `rank_between_21_and_23` | Clean build passed; both bounds unconditional |
| General affine row/column coset lemma | `set_affine_row_or_column_coset` | Compiled for any matrix set with at least four elements and pairwise rank-one differences; no tensor-decomposition assumption |
| All subspaces and two-planes in the actual matrix space | `FullSubspaceCount.mat3_all_subspace_count`, `FullSubspaceCount.mat3_two_plane_count` | Compiled: 8,283,458 subspaces and 43,435 two-planes |
| Actual all-high two-plane count | `AllHighCount.all_high_plane_count`, `AllHighCount.high_pair_count` | Compiled: 32,018 actual planes and 192,108 eligible ordered matrix pairs, with a proved six-to-one basis correspondence |
| Actual two-plane quotient occupation domain | `FullSubspaceCount.plane_quotient_nonzero_card`, `FullSubspaceCount.plane_quotient_nonzero_proper_subspace_count` | Compiled for every two-dimensional subspace: 127 nonzero quotient elements and 29,210 nonzero proper quotient subspaces |
| Every selected row is a strict proper superspace | `plane484SourceStrict`, `plane484DeadStrict` through their plane-491 versions | Compiled for all 5,917 source/dead rows; separating functionals prove strictness, not just Boolean containment |
| First-row quotient is rectangular multiplication | `firstRow_quotient_decomp_iff`, `firstRow_quotient_rankAtLeast_iff`, `firstRowTensorEquiv_tensor` | Compiled in both directions for all lengths; the tensor equivalence uses the actual six-dimensional output support |
| General quotient/restricted-input identification | `QuotientRestriction.quotientEquiv`, `QuotientRestriction.nonempty_quotient_iff_restricted`, `QuotientRestriction.quotientRankAtLeast_iff_restricted` | Compiled for every matrix subspace and all lengths, with arbitrary restricted linear forms and the actual trace pairing; 24 declaration guards passed |
| Normalized-coset hyperplanes and exhaustive indexing | `NormalizedCosetCount.normalizedCosetSpan_hyperplane_count`, `NormalizedCosetCount.affine_hyperplane_count`, `NormalizedCosetCount.affine_hyperplane_complete` | Compiled: 15 actual hyperplanes, 14 excluding the first-row subspace; the named family is bijective, not merely a list of examples |
| Selected frozen-table values bound all retained rows | `FrozenWang.plane484_source`, `FrozenWang.plane484_dead` through their plane-491 versions | Compiled for all 5,917 rows against an explicit GL/transpose orbit expansion; no assumed transport or table-value facts |
| All frozen representative rank bounds | `FrozenRegistry.all_representatives` and `FrozenRegistry.repNNN` for all 496 indices | Parent compilation and all 496 exact-type/axiom guards passed at the actual frozen bases and labels; the checked complement is empty |
| Unconditional global frozen-table rank soundness | `FrozenRegistry.L0_rank_sound`, `FrozenRegistry.coverage_with_rank_bound` | Parent compilation and all three global exact-type/axiom guards passed for every actual matrix subspace; no representative-bound assumptions remain |
| Additional representative bounds | `FrozenRank.rep024`, `GlobalOrbit.Unused.rep181`, `GlobalOrbit.Unused.rep184`, `GlobalOrbit.Unused.rep203`, `GlobalOrbit.Unused.rep273`, `GlobalOrbit.Unused.rep284`, `GlobalOrbit.Unused.rep291`, `FrozenRegistry.rep418` | Parent compilation and exact-type/axiom tests passed. All eight are consolidated into the registry; the node-418 consequence uses the proved node-284 bound |
| Exact normalized-span and representative frozen values | `FrozenL0Report.normalized_L0_exact`, `FrozenL0Report.first_row_L0_exact`, `FrozenL0Report.all_high_representative_L0_exact` | Compiled: L0(S)=14, L0(R)=15 and L0=18 at each of the eight actual all-high representatives; higher labels excluded by proved rank-count invariance |
| Exact line and affine-hyperplane frozen values | `FrozenL0Report.nonzero_line_L0_exact`, `FrozenL0Report.one_dimensional_L0_exact`, `FrozenL0Report.affine_hyperplane_L0_exact` | Parent compilation and exact-type/axiom tests passed: every actual line has L0=19 and all fourteen specified hyperplanes have L0=17 |
| Complete two-plane orbit classification and exact sizes | `PlaneOrbit.FullClassification.frozen_classification`, `PlaneOrbit.FullClassification.frozen_orbit_sizes`, `PlaneOrbit.FullClassification.frozen_representatives_inequivalent` | Parent integration passed: 387 modules, zero failures, followed by exact-type/axiom tests of the combined entry point. Covers all actual two-dimensional submodules through the existing frozen direct-action predicate |
| Frozen representative coverage in every dimension | `GlobalOrbit.frozen_coverage`, `GlobalOrbit.all_dimensions_covered` | Parent compilation passed for all 71 coverage modules and tests. Arbitrary subspaces reduce to representative extensions; all 15,807 normalized cases are kernel checked. This does not assert global label consistency or rank soundness |
| Frozen labels agree with L0 on dimensions zero through two | `FrozenLabel.small_representative_exact` | Parent compilation and axiom guards passed for indices 478--495; global consistency remains separate |
| Global frozen label consistency and exact orbit values | `FrozenLabel.frozen_labels_consistent`, `FrozenLabel.all_representatives_exact`, `FrozenLabel.L0_exact_of_orbit` | Parent compilation and exact-type/axiom guards passed for all dimensions; overlapping orbits have the same label. This is not rank soundness |
| Concrete calibration decomposition and quotient coordinates | `Calibration.fixture`, `Calibration.coordinates`, `Calibration.projected_A_eq`, `Calibration.projected_A_not_mem` | Parent compilation passed: 729 tensor entries, eight whole-quotient charts, actual projected factors and nonzero quotient directions |
| Calibration occupation weights and finite row sums | `Calibration.weight_total`, `Calibration.weight_eq_coordinateWeight`, `Calibration.quotientMass_eq_pointMass` | Parent compilation passed; actual weights and quotient masses agree with the finite coordinate representation |
| Complete stored-label calibration checks | `Calibration.tableRow_controls`, `Calibration.singleton_cap_distribution` | Parent compilation passed for all 29,210 rows in all eight quotients, both control families, and singleton histograms |
| Complete concrete calibration row catalogue | `CalibrationRows.rowBasis484_complete` through `CalibrationRows.rowBasis491_complete` | Parent compilation and 40 declaration axiom guards passed. Each actual strict proper superspace has a unique row, and row masks agree with actual quotient membership |
| Actual-row labels equal mathematical L0 | `Calibration.exactL0`, `Calibration.orbitRecordAt_valid` | Parent compilation passed for all 233,680 row-orbit bindings and their aggregate, with exact-type and standard-axiom checks |
| Full target-19 and projected rank-23 occupation controls | `Calibration.target19_feasible`, `Calibration.projected23_feasible`, `Calibration.projectedFixture_feasible` | Parent compilation and exact-type/axiom tests passed for all eight full systems. Occupation feasibility is not a tensor-decomposition existence claim |
| Exact capacities on actual quotient directions | `Calibration.actual_cap_distribution`, `Calibration.actual_seven_boolean_caps`, `Calibration.actual_orbit489_unique_cap_two` | Parent compilation and exact-type/axiom tests passed; all eight histograms use mathematical L0 and include the exceptional unique cap-two direction |
| Eight full frozen-table occupation systems have no integer model | `FrozenOccupation.plane484_no_model` through `FrozenOccupation.plane491_no_model` | Compiled for arbitrary integer weights on actual nonzero quotient directions; exact types and all eight axiom guards passed |
| Integer multiplicities and Boolean copies are equivalent | `Qiushi.CNF.bounded_integer_iff_copies`, `Qiushi.CNF.copy_occupation` | Compiled including zero caps and finite row sums |
| Disjoint sequential counters encode the occupation system | `Qiushi.CNF.occupation_cnf_equisatisfiable`, `Qiushi.CNF.singleton_occupation_cnf_equisatisfiable` | Compiled for an actual `Std.Sat.CNF`; the singleton-cap version states its cap-source hypothesis explicitly |
| Transparent exact-prefix encoding | `Qiushi.CNF.exactPrefixCNF_correct` | Compiled with the necessary positive input-length hypothesis; the alternative two-counter encoding handles empty inputs |

The six groups in `verification.json` select 89 terminal declarations and
their complete dependencies. All groups passed fresh kernel replay from an
empty environment, including the main theorem, all 496 representative bounds,
calibration, classification, full occupation systems, supplementary structural
results and encoding semantics. Every checked root's transitive axioms are
contained in `{propext, Classical.choice, Quot.sound}`. All 13,438 registered
modules have source-matched successful build outputs. [STATUS.md](STATUS.md)
and [verification-results.json](verification-results.json) record the outcomes.

## Scope Notes

- `TensorEntryDecomp` permits zero summands. The padded-decomposition results
  now make that case explicit. The lower bound 21 alone cannot exclude a
  length-21 decomposition padded to length 22.
- The E11 count, dimension partition and complete semantic row index have
  compiled; 14 further declarations passed the standard-axiom checks. This
  does not certify the ordering or numeric lower-bound values of a historical
  saved Python cache. Such values are not assumed by the count theorem.
- Discussion that a necessary condition does not yet prove existence is not
  a constructed mathematical counterexample. Neither a rank-21/rank-22
  construction nor a core-rank-19 witness is claimed by these proofs.
- The main theorem and all eight finite premises passed a clean 8,455-module
  local-source build, followed by the combined main/registry fresh replay.
  No finite-bound assumption remains in the main theorem.
- `QiushiReport.lean` and its exact-statement tests passed using the clean core
  imports, including the full occupation results, normalized-coset counts and
  encoding semantics. The 32,018 all-high count also passed parent integration;
  individual orbit cardinalities and the full 14-orbit partition have passed
  parent compilation. The combined entry point and its exact-type/axiom tests
  passed with the new classification and exact frozen values integrated.
- The mathematically defined frozen orbit expansion and the universal
  counter-CNF semantics are not formal proofs of equality with the saved
  Python cache or DIMACS bytes. PySAT's implementation and the original DRAT
  executions are outside these newly proved interfaces. The main theorem
  instead uses its fully proved integer branch certificates.
