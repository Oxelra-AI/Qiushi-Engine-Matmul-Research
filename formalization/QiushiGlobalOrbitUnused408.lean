import QiushiGlobalOrbitUnused408Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep408 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 408))
      (frozenWangTable.lower 408) := by
  rw [show frozenWangTable.basis 408 = [262,163,84,10] by decide +kernel,
      show frozenWangTable.lower 408 = 17 by decide +kernel]
  exact plane408UnusedGen_lb17

end QiushiMatmul.GlobalOrbit.Unused
