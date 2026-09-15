import QiushiGlobalOrbitUnused392Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep392 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 392))
      (frozenWangTable.lower 392) := by
  rw [show frozenWangTable.basis 392 = [259,68,20,10] by decide +kernel,
      show frozenWangTable.lower 392 = 17 by decide +kernel]
  exact plane392UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
