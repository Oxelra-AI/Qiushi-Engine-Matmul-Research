import QiushiGlobalOrbitUnused356Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep356 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 356))
      (frozenWangTable.lower 356) := by
  rw [show frozenWangTable.basis 356 = [290,96,20,1] by decide +kernel,
      show frozenWangTable.lower 356 = 17 by decide +kernel]
  exact plane356UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
