import QiushiGlobalOrbitUnused88Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep088 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 88))
      (frozenWangTable.lower 88) := by
  rw [show frozenWangTable.basis 88 = [80,8,4,2,1] by decide +kernel,
      show frozenWangTable.lower 88 = 13 by decide +kernel]
  exact plane88UnusedGen_lb13

end QiushiMatmul.GlobalOrbit.Unused
