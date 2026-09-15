import QiushiGlobalOrbitUnused181Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep181 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 181))
      (frozenWangTable.lower 181) := by
  rw [show frozenWangTable.basis 181 = [258,84,32,10,1] by decide +kernel,
      show frozenWangTable.lower 181 = 15 by decide +kernel]
  exact plane181UnusedGen_lb15

end QiushiMatmul.GlobalOrbit.Unused
