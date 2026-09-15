import QiushiGlobalOrbitUnused371Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep371 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 371))
      (frozenWangTable.lower 371) := by
  rw [show frozenWangTable.basis 371 = [290,224,20,1] by decide +kernel,
      show frozenWangTable.lower 371 = 17 by decide +kernel]
  exact plane371UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
