import QiushiGlobalOrbitUnused337Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep337 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 337))
      (frozenWangTable.lower 337) := by
  rw [show frozenWangTable.basis 337 = [258,98,16,1] by decide +kernel,
      show frozenWangTable.lower 337 = 16 by decide +kernel]
  exact plane337UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
