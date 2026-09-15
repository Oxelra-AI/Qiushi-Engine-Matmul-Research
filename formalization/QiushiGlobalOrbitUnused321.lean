import QiushiGlobalOrbitUnused321Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep321 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 321))
      (frozenWangTable.lower 321) := by
  rw [show frozenWangTable.basis 321 = [306,160,10,1] by decide +kernel,
      show frozenWangTable.lower 321 = 17 by decide +kernel]
  exact plane321UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
