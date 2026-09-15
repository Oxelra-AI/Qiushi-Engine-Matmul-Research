import QiushiOccupationCNF
import QiushiExactPrefixCNF

set_option pp.universes true
set_option format.width 110

#check @Qiushi.CNF.bit_false
#print axioms Qiushi.CNF.bit_false
#check @Qiushi.CNF.bit_true
#print axioms Qiushi.CNF.bit_true
#check @Qiushi.CNF.bit_le_one
#print axioms Qiushi.CNF.bit_le_one
#check @Qiushi.CNF.copyCount_le
#print axioms Qiushi.CNF.copyCount_le
#check @Qiushi.CNF.threshold_sum
#print axioms Qiushi.CNF.threshold_sum
#check @Qiushi.CNF.copyCount_threshold
#print axioms Qiushi.CNF.copyCount_threshold
#check @Qiushi.CNF.bounded_iff_copies
#print axioms Qiushi.CNF.bounded_iff_copies
#check @Qiushi.CNF.bounded_integer_iff_copies
#print axioms Qiushi.CNF.bounded_integer_iff_copies
#check @Qiushi.CNF.bounded_system_iff_copies
#print axioms Qiushi.CNF.bounded_system_iff_copies
#check @Qiushi.CNF.row_sum_copies
#print axioms Qiushi.CNF.row_sum_copies
#check @Qiushi.CNF.occupation_iff_copies
#print axioms Qiushi.CNF.occupation_iff_copies
#check @Qiushi.CNF.threshold_monotone
#print axioms Qiushi.CNF.threshold_monotone
#check @Qiushi.CNF.prefix_zero
#print axioms Qiushi.CNF.prefix_zero
#check @Qiushi.CNF.prefix_succ
#print axioms Qiushi.CNF.prefix_succ
#check @Qiushi.CNF.prefix_le
#print axioms Qiushi.CNF.prefix_le
#check @Qiushi.CNF.thresholds_forward
#print axioms Qiushi.CNF.thresholds_forward
#check @Qiushi.CNF.forward_forces
#print axioms Qiushi.CNF.forward_forces
#check @Qiushi.CNF.forward_atmost_iff
#print axioms Qiushi.CNF.forward_atmost_iff
#check @Qiushi.CNF.sat_ofClauses
#print axioms Qiushi.CNF.sat_ofClauses
#check @Qiushi.CNF.clause_imp
#print axioms Qiushi.CNF.clause_imp
#check @Qiushi.CNF.clause_inc
#print axioms Qiushi.CNF.clause_inc
#check @Qiushi.CNF.sat_forwardStep
#print axioms Qiushi.CNF.sat_forwardStep
#check @Qiushi.CNF.sat_forwardCNF
#print axioms Qiushi.CNF.sat_forwardCNF
#check @Qiushi.CNF.sat_atMostCNF
#print axioms Qiushi.CNF.sat_atMostCNF
#check @Qiushi.CNF.atMostCNF_correct
#print axioms Qiushi.CNF.atMostCNF_correct
#check @Qiushi.CNF.sat_conjoin
#print axioms Qiushi.CNF.sat_conjoin
#check @Qiushi.CNF.shared_comp_embed
#print axioms Qiushi.CNF.shared_comp_embed
#check @Qiushi.CNF.auxiliary_blocks_disjoint
#print axioms Qiushi.CNF.auxiliary_blocks_disjoint
#check @Qiushi.CNF.sat_familyCNF
#print axioms Qiushi.CNF.sat_familyCNF
#check @Qiushi.CNF.disjoint_extensions_iff
#print axioms Qiushi.CNF.disjoint_extensions_iff
#check @Qiushi.CNF.duplicate_cnf
#print axioms Qiushi.CNF.duplicate_cnf
#check @Qiushi.CNF.omit_satisfied_cnf
#print axioms Qiushi.CNF.omit_satisfied_cnf
#check @Qiushi.CNF.clauses_subset_preserves_sat
#print axioms Qiushi.CNF.clauses_subset_preserves_sat
#check @Qiushi.CNF.sat_dedupCNF
#print axioms Qiushi.CNF.sat_dedupCNF
#check @Qiushi.CNF.eval_dedup_literals
#print axioms Qiushi.CNF.eval_dedup_literals
#check @Qiushi.CNF.tautological_clause
#print axioms Qiushi.CNF.tautological_clause
#check @Qiushi.CNF.prefix_sum
#print axioms Qiushi.CNF.prefix_sum
#check @Qiushi.CNF.prefix_complement
#print axioms Qiushi.CNF.prefix_complement
#check @Qiushi.CNF.prefix_eq_zero
#print axioms Qiushi.CNF.prefix_eq_zero
#check @Qiushi.CNF.rowCNF_correct
#print axioms Qiushi.CNF.rowCNF_correct
#check @Qiushi.CNF.eval_flip_clause
#print axioms Qiushi.CNF.eval_flip_clause
#check @Qiushi.CNF.sat_flipPrimary
#print axioms Qiushi.CNF.sat_flipPrimary
#check @Qiushi.CNF.atLeastCNF_correct
#print axioms Qiushi.CNF.atLeastCNF_correct
#check @Qiushi.CNF.exact_two_counters
#print axioms Qiushi.CNF.exact_two_counters
#check @Qiushi.CNF.previous_thresholds
#print axioms Qiushi.CNF.previous_thresholds
#check @Qiushi.CNF.thresholds_reverse
#print axioms Qiushi.CNF.thresholds_reverse
#check @Qiushi.CNF.reverse_bounds
#print axioms Qiushi.CNF.reverse_bounds
#check @Qiushi.CNF.clause_or
#print axioms Qiushi.CNF.clause_or
#check @Qiushi.CNF.sat_reverseStep
#print axioms Qiushi.CNF.sat_reverseStep
#check @Qiushi.CNF.sat_reverseCNF
#print axioms Qiushi.CNF.sat_reverseCNF
#check @Qiushi.CNF.sat_exactPrefixCNF
#print axioms Qiushi.CNF.sat_exactPrefixCNF
#check @Qiushi.CNF.exactPrefixCNF_correct
#print axioms Qiushi.CNF.exactPrefixCNF_correct
#check @Qiushi.CNF.prefix_fin_sum
#print axioms Qiushi.CNF.prefix_fin_sum
#check @Qiushi.CNF.setSignal_count
#print axioms Qiushi.CNF.setSignal_count
#check @Qiushi.CNF.sat_finiteRowCNF
#print axioms Qiushi.CNF.sat_finiteRowCNF
#check @Qiushi.CNF.exists_uncurry
#print axioms Qiushi.CNF.exists_uncurry
#check @Qiushi.CNF.finiteRowCNF_correct
#print axioms Qiushi.CNF.finiteRowCNF_correct
#check @Qiushi.CNF.booleanSystemCNF_correct
#print axioms Qiushi.CNF.booleanSystemCNF_correct
#check @Qiushi.CNF.copy_total
#print axioms Qiushi.CNF.copy_total
#check @Qiushi.CNF.copy_row_int
#print axioms Qiushi.CNF.copy_row_int
#check @Qiushi.CNF.copy_occupation
#print axioms Qiushi.CNF.copy_occupation
#check @Qiushi.CNF.sat_occupationCNF
#print axioms Qiushi.CNF.sat_occupationCNF
#check @Qiushi.CNF.occupationCNF_for_copies
#print axioms Qiushi.CNF.occupationCNF_for_copies
#check @Qiushi.CNF.occupation_cnf_equisatisfiable
#print axioms Qiushi.CNF.occupation_cnf_equisatisfiable
#check @Qiushi.CNF.occupation_count_le_total
#print axioms Qiushi.CNF.occupation_count_le_total
#check @Qiushi.CNF.singleton_caps_entailed
#print axioms Qiushi.CNF.singleton_caps_entailed
#check @Qiushi.CNF.singleton_occupation_cnf_equisatisfiable
#print axioms Qiushi.CNF.singleton_occupation_cnf_equisatisfiable

#print Qiushi.CNF.Copies
#print Qiushi.CNF.copyCount
#print Qiushi.CNF.Occupation
#print Qiushi.CNF.Forward
#print Qiushi.CNF.Reverse
#print Qiushi.CNF.SingletonCapSource
#print Qiushi.CNF.clippedCaps
#print Qiushi.CNF.occupationCNF
