import QiushiGlobalOrbitUnused203Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep203 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 203))
      (frozenWangTable.lower 203) := by
  rw [show frozenWangTable.basis 203 = [272,176,68,10,1] by decide +kernel,
      show frozenWangTable.lower 203 = 16 by decide +kernel]
  exact plane203UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
