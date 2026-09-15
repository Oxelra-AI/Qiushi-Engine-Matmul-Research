import QiushiGlobalOrbitUnused399Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep399 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 399))
      (frozenWangTable.lower 399) := by
  rw [show frozenWangTable.basis 399 = [164,96,20,10] by decide +kernel,
      show frozenWangTable.lower 399 = 17 by decide +kernel]
  exact plane399UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
