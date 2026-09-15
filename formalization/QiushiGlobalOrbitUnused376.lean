import QiushiGlobalOrbitUnused376Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep376 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 376))
      (frozenWangTable.lower 376) := by
  rw [show frozenWangTable.basis 376 = [160,68,19,10] by decide +kernel,
      show frozenWangTable.lower 376 = 17 by decide +kernel]
  exact plane376UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
