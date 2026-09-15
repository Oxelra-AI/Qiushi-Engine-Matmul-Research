import QiushiGlobalOrbitUnused304Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep304 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 304))
      (frozenWangTable.lower 304) := by
  rw [show frozenWangTable.basis 304 = [256,84,10,1] by decide +kernel,
      show frozenWangTable.lower 304 = 16 by decide +kernel]
  exact plane304UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
