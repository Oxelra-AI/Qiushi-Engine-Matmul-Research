import QiushiGlobalOrbitUnused307Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep307 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 307))
      (frozenWangTable.lower 307) := by
  rw [show frozenWangTable.basis 307 = [272,96,10,1] by decide +kernel,
      show frozenWangTable.lower 307 = 17 by decide +kernel]
  exact plane307UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
