import QiushiGlobalOrbitUnused333Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep333 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 333))
      (frozenWangTable.lower 333) := by
  rw [show frozenWangTable.basis 333 = [298,96,16,1] by decide +kernel,
      show frozenWangTable.lower 333 = 16 by decide +kernel]
  exact plane333UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
