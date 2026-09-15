import QiushiGlobalOrbitUnused395Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep395 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 395))
      (frozenWangTable.lower 395) := by
  rw [show frozenWangTable.basis 395 = [131,96,20,10] by decide +kernel,
      show frozenWangTable.lower 395 = 17 by decide +kernel]
  exact plane395UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
