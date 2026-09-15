import QiushiGlobalOrbitUnused248Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep248 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 248))
      (frozenWangTable.lower 248) := by
  rw [show frozenWangTable.basis 248 = [8,4,2,1] by decide +kernel,
      show frozenWangTable.lower 248 = 14 by decide +kernel]
  exact plane248UnusedGen_lb14

end QiushiMatmul.GlobalOrbit.Unused
