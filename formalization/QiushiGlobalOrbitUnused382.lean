import QiushiGlobalOrbitUnused382Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep382 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 382))
      (frozenWangTable.lower 382) := by
  rw [show frozenWangTable.basis 382 = [262,68,19,10] by decide +kernel,
      show frozenWangTable.lower 382 = 17 by decide +kernel]
  exact plane382UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
