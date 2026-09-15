import QiushiGlobalOrbitUnused284Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep284 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 284))
      (frozenWangTable.lower 284) := by
  rw [show frozenWangTable.basis 284 = [68,20,10,1] by decide +kernel,
      show frozenWangTable.lower 284 = 17 by decide +kernel]
  exact plane284UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
