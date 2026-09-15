import QiushiGlobalOrbitUnused402Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep402 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 402))
      (frozenWangTable.lower 402) := by
  rw [show frozenWangTable.basis 402 = [391,96,20,10] by decide +kernel,
      show frozenWangTable.lower 402 = 17 by decide +kernel]
  exact plane402UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
