import QiushiGlobalOrbitUnused184Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep184 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 184))
      (frozenWangTable.lower 184) := by
  rw [show frozenWangTable.basis 184 = [386,84,32,10,1] by decide +kernel,
      show frozenWangTable.lower 184 = 15 by decide +kernel]
  exact plane184UnusedGen_lb15

end QiushiMatmul.GlobalOrbit.Unused
