import QiushiGlobalOrbitUnused379Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep379 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 379))
      (frozenWangTable.lower 379) := by
  rw [show frozenWangTable.basis 379 = [164,68,19,10] by decide +kernel,
      show frozenWangTable.lower 379 = 17 by decide +kernel]
  exact plane379UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
