import QiushiGlobalOrbitUnused249Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep249 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 249))
      (frozenWangTable.lower 249) := by
  rw [show frozenWangTable.basis 249 = [80,4,2,1] by decide +kernel,
      show frozenWangTable.lower 249 = 14 by decide +kernel]
  exact plane249UnusedGen_lb14

end QiushiMatmul.GlobalOrbit.Unused
