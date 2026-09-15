import QiushiGlobalOrbitUnused386Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep386 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 386))
      (frozenWangTable.lower 386) := by
  rw [show frozenWangTable.basis 386 = [161,68,20,10] by decide +kernel,
      show frozenWangTable.lower 386 = 17 by decide +kernel]
  exact plane386UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
