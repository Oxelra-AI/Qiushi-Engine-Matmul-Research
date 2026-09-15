import QiushiGlobalOrbitUnused240Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep240 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 240))
      (frozenWangTable.lower 240) := by
  rw [show frozenWangTable.basis 240 = [261,161,68,19,10] by decide +kernel,
      show frozenWangTable.lower 240 = 16 by decide +kernel]
  exact plane240UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
