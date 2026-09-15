import QiushiGlobalOrbitUnused328Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep328 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 328))
      (frozenWangTable.lower 328) := by
  rw [show frozenWangTable.basis 328 = [140,96,16,1] by decide +kernel,
      show frozenWangTable.lower 328 = 16 by decide +kernel]
  exact plane328UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
