import FrozenRegistry.All
import QiushiGlobalOrbitRankSoundness

namespace QiushiMatmul.FrozenRegistry

theorem L0_rank_sound (W : Submodule F2 Mat3) :
    QuotientRankAtLeast W (frozenWangTable.L0 W) :=
  GlobalOrbit.L0_rank_sound_of_representatives frozenWangTable all_representatives W

theorem coverage_with_rank_bound (W : Submodule F2 Mat3) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W ∧
      QuotientRankAtLeast W (frozenWangTable.lower i) :=
  GlobalOrbit.frozen_coverage_with_rank_bound all_representatives W

end QiushiMatmul.FrozenRegistry
