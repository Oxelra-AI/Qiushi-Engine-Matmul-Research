import QiushiGlobalOrbitUnused355Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep355 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 355))
      (frozenWangTable.lower 355) := by
  rw [show frozenWangTable.basis 355 = [164,96,20,1] by decide +kernel,
      show frozenWangTable.lower 355 = 17 by decide +kernel]
  exact plane355UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
