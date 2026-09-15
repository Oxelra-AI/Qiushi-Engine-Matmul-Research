import QiushiGlobalOrbitUnused353Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep353 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 353))
      (frozenWangTable.lower 353) := by
  rw [show frozenWangTable.basis 353 = [196,38,20,1] by decide +kernel,
      show frozenWangTable.lower 353 = 17 by decide +kernel]
  exact plane353UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
