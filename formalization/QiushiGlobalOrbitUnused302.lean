import QiushiGlobalOrbitUnused302Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep302 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 302))
      (frozenWangTable.lower 302) := by
  rw [show frozenWangTable.basis 302 = [304,68,10,1] by decide +kernel,
      show frozenWangTable.lower 302 = 17 by decide +kernel]
  exact plane302UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
