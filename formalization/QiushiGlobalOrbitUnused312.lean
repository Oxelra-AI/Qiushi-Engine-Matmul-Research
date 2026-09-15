import QiushiGlobalOrbitUnused312Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep312 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 312))
      (frozenWangTable.lower 312) := by
  rw [show frozenWangTable.basis 312 = [386,96,10,1] by decide +kernel,
      show frozenWangTable.lower 312 = 17 by decide +kernel]
  exact plane312UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
