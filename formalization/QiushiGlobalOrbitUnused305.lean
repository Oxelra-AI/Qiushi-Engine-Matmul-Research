import QiushiGlobalOrbitUnused305Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep305 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 305))
      (frozenWangTable.lower 305) := by
  rw [show frozenWangTable.basis 305 = [258,84,10,1] by decide +kernel,
      show frozenWangTable.lower 305 = 17 by decide +kernel]
  exact plane305UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
