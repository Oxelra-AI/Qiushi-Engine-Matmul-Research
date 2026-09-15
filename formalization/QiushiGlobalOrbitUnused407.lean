import QiushiGlobalOrbitUnused407Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep407 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 407))
      (frozenWangTable.lower 407) := by
  rw [show frozenWangTable.basis 407 = [257,163,84,10] by decide +kernel,
      show frozenWangTable.lower 407 = 17 by decide +kernel]
  exact plane407UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
