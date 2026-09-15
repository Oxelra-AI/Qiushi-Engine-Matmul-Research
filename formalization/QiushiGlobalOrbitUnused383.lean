import QiushiGlobalOrbitUnused383Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep383 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 383))
      (frozenWangTable.lower 383) := by
  rw [show frozenWangTable.basis 383 = [289,68,19,10] by decide +kernel,
      show frozenWangTable.lower 383 = 17 by decide +kernel]
  exact plane383UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
