import QiushiFrozenLabelKeys
import QiushiFrozenLabelCollisions

namespace QiushiMatmul.FrozenLabel

theorem labels_eq_of_overlap (i j : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    frozenWangLower i = frozenWangLower j := by
  by_contra hne
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact collisionPairs_no_overlap i j
      (different_label_overlap_candidate i j hlt hne W hi hj) W hi hj
  · exact hne (congrArg frozenWangLower (Fin.ext heq))
  · exact collisionPairs_no_overlap j i
      (different_label_overlap_candidate j i hgt (Ne.symm hne) W hj hi) W hj hi

theorem frozen_labels_consistent : LabelConsistent := labels_eq_of_overlap

theorem all_representatives_exact (i : Fin 496) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i :=
  label_consistent_iff_exact_representatives.mp frozen_labels_consistent i

theorem L0_exact_of_orbit (i : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) : frozenWangTable.L0 W = frozenWangLower i :=
  exact_of_label_consistent frozen_labels_consistent i hi

end QiushiMatmul.FrozenLabel
