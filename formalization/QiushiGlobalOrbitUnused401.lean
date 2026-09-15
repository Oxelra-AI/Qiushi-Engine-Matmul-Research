import QiushiGlobalOrbitUnused401Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep401 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 401))
      (frozenWangTable.lower 401) := by
  rw [show frozenWangTable.basis 401 = [261,96,20,10] by decide +kernel,
      show frozenWangTable.lower 401 = 17 by decide +kernel]
  exact plane401UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
