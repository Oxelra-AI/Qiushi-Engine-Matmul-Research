import QiushiGlobalOrbitUnused301Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep301 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 301))
      (frozenWangTable.lower 301) := by
  rw [show frozenWangTable.basis 301 = [176,68,10,1] by decide +kernel,
      show frozenWangTable.lower 301 = 17 by decide +kernel]
  exact plane301UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
