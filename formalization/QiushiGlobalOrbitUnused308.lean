import QiushiGlobalOrbitUnused308Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep308 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 308))
      (frozenWangTable.lower 308) := by
  rw [show frozenWangTable.basis 308 = [288,96,10,1] by decide +kernel,
      show frozenWangTable.lower 308 = 16 by decide +kernel]
  exact plane308UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
