import QiushiGlobalOrbitUnused309Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep309 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 309))
      (frozenWangTable.lower 309) := by
  rw [show frozenWangTable.basis 309 = [290,96,10,1] by decide +kernel,
      show frozenWangTable.lower 309 = 17 by decide +kernel]
  exact plane309UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
