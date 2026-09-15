import QiushiGlobalOrbitUnused306Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep306 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 306))
      (frozenWangTable.lower 306) := by
  rw [show frozenWangTable.basis 306 = [132,96,10,1] by decide +kernel,
      show frozenWangTable.lower 306 = 17 by decide +kernel]
  exact plane306UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
