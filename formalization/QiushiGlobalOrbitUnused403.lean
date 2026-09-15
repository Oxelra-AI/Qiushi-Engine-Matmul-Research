import QiushiGlobalOrbitUnused403Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep403 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 403))
      (frozenWangTable.lower 403) := by
  rw [show frozenWangTable.basis 403 = [304,161,68,10] by decide +kernel,
      show frozenWangTable.lower 403 = 17 by decide +kernel]
  exact plane403UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
