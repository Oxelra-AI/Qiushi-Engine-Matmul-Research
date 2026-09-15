import QiushiGlobalOrbitUnused404Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep404 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 404))
      (frozenWangTable.lower 404) := by
  rw [show frozenWangTable.basis 404 = [309,162,68,10] by decide +kernel,
      show frozenWangTable.lower 404 = 17 by decide +kernel]
  exact plane404UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
