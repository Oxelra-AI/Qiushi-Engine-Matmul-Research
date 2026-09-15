import QiushiGlobalOrbitUnused387Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep387 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 387))
      (frozenWangTable.lower 387) := by
  rw [show frozenWangTable.basis 387 = [162,68,20,10] by decide +kernel,
      show frozenWangTable.lower 387 = 17 by decide +kernel]
  exact plane387UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
