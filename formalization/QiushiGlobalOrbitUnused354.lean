import QiushiGlobalOrbitUnused354Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep354 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 354))
      (frozenWangTable.lower 354) := by
  rw [show frozenWangTable.basis 354 = [136,96,20,1] by decide +kernel,
      show frozenWangTable.lower 354 = 17 by decide +kernel]
  exact plane354UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
