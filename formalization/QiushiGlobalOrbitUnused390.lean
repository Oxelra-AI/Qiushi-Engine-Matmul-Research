import QiushiGlobalOrbitUnused390Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep390 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 390))
      (frozenWangTable.lower 390) := by
  rw [show frozenWangTable.basis 390 = [167,68,20,10] by decide +kernel,
      show frozenWangTable.lower 390 = 17 by decide +kernel]
  exact plane390UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
