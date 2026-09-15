import QiushiGlobalOrbitUnused289Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep289 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 289))
      (frozenWangTable.lower 289) := by
  rw [show frozenWangTable.basis 289 = [258,20,10,1] by decide +kernel,
      show frozenWangTable.lower 289 = 17 by decide +kernel]
  exact plane289UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
