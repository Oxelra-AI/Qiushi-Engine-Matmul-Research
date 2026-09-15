import QiushiGlobalOrbitRankSoundness

namespace QiushiMatmul.GlobalOrbit

example (table : FrozenOrbitTable)
    (hrep : ∀ i : Fin 496,
      QuotientRankAtLeast (spanCodes (table.basis i)) (table.lower i))
    (W : Submodule F2 Mat3) : QuotientRankAtLeast W (table.L0 W) :=
  L0_rank_sound_of_representatives table hrep W

example :
    (∀ W : Submodule F2 Mat3, QuotientRankAtLeast W (frozenWangTable.L0 W)) ↔
      ∀ i : Fin 496,
        QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
          (frozenWangTable.lower i) := frozen_L0_rank_sound_iff_representatives

example (hrep : ∀ i : Fin 496,
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis i)) (frozenWangTable.lower i))
    (W : Submodule F2 Mat3) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W ∧
      QuotientRankAtLeast W (frozenWangTable.lower i) :=
  frozen_coverage_with_rank_bound hrep W

#print axioms rank_bound_of_orbit_image
#print axioms L0_rank_sound_of_representatives
#print axioms frozen_L0_rank_sound_iff_representatives
#print axioms frozen_coverage_with_rank_bound

end QiushiMatmul.GlobalOrbit
