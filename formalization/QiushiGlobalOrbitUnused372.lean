import QiushiGlobalOrbitUnused372Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep372 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 372))
      (frozenWangTable.lower 372) := by
  rw [show frozenWangTable.basis 372 = [298,224,20,1] by decide +kernel,
      show frozenWangTable.lower 372 = 17 by decide +kernel]
  exact plane372UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
