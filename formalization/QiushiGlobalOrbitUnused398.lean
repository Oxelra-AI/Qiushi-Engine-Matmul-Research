import QiushiGlobalOrbitUnused398Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep398 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 398))
      (frozenWangTable.lower 398) := by
  rw [show frozenWangTable.basis 398 = [161,96,20,10] by decide +kernel,
      show frozenWangTable.lower 398 = 17 by decide +kernel]
  exact plane398UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
