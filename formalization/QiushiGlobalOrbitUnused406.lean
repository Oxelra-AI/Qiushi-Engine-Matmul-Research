import QiushiGlobalOrbitUnused406Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep406 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 406))
      (frozenWangTable.lower 406) := by
  rw [show frozenWangTable.basis 406 = [276,179,68,10] by decide +kernel,
      show frozenWangTable.lower 406 = 17 by decide +kernel]
  exact plane406UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
