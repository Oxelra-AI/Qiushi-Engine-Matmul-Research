import QiushiGlobalOrbitUnused92Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep092 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 92))
      (frozenWangTable.lower 92) := by
  rw [show frozenWangTable.basis 92 = [160,80,4,2,1] by decide +kernel,
      show frozenWangTable.lower 92 = 13 by decide +kernel]
  exact plane92UnusedGen_lb13

end QiushiMatmul.GlobalOrbit.Unused
