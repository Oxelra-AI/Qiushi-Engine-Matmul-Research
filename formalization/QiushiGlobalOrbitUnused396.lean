import QiushiGlobalOrbitUnused396Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep396 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 396))
      (frozenWangTable.lower 396) := by
  rw [show frozenWangTable.basis 396 = [133,96,20,10] by decide +kernel,
      show frozenWangTable.lower 396 = 17 by decide +kernel]
  exact plane396UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
