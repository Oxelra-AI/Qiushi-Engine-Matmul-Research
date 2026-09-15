import QiushiGlobalOrbitUnused291Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep291 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 291))
      (frozenWangTable.lower 291) := by
  rw [show frozenWangTable.basis 291 = [84,32,10,1] by decide +kernel,
      show frozenWangTable.lower 291 = 16 by decide +kernel]
  exact plane291UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
