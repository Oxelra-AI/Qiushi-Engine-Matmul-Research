import QiushiGlobalOrbitUnused389Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep389 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 389))
      (frozenWangTable.lower 389) := by
  rw [show frozenWangTable.basis 389 = [166,68,20,10] by decide +kernel,
      show frozenWangTable.lower 389 = 17 by decide +kernel]
  exact plane389UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
