import QiushiGlobalOrbitUnused378Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep378 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 378))
      (frozenWangTable.lower 378) := by
  rw [show frozenWangTable.basis 378 = [162,68,19,10] by decide +kernel,
      show frozenWangTable.lower 378 = 17 by decide +kernel]
  exact plane378UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
