import QiushiGlobalOrbitUnused339Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep339 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 339))
      (frozenWangTable.lower 339) := by
  rw [show frozenWangTable.basis 339 = [296,98,16,1] by decide +kernel,
      show frozenWangTable.lower 339 = 16 by decide +kernel]
  exact plane339UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
