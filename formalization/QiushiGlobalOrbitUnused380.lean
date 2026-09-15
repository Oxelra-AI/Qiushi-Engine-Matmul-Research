import QiushiGlobalOrbitUnused380Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep380 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 380))
      (frozenWangTable.lower 380) := by
  rw [show frozenWangTable.basis 380 = [258,68,19,10] by decide +kernel,
      show frozenWangTable.lower 380 = 17 by decide +kernel]
  exact plane380UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
