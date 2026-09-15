import QiushiGlobalOrbitUnused394Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep394 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 394))
      (frozenWangTable.lower 394) := by
  rw [show frozenWangTable.basis 394 = [289,68,20,10] by decide +kernel,
      show frozenWangTable.lower 394 = 17 by decide +kernel]
  exact plane394UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
