import QiushiGlobalOrbitUnused388Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep388 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 388))
      (frozenWangTable.lower 388) := by
  rw [show frozenWangTable.basis 388 = [164,68,20,10] by decide +kernel,
      show frozenWangTable.lower 388 = 17 by decide +kernel]
  exact plane388UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
