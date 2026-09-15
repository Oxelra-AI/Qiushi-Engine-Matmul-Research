import QiushiGlobalOrbitUnused273Final
import QiushiFrozenWangData

namespace QiushiMatmul.GlobalOrbit.Unused

theorem rep273 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 273))
      (frozenWangTable.lower 273) := by
  rw [show frozenWangTable.basis 273 = [156,80,2,1] by decide +kernel,
      show frozenWangTable.lower 273 = 16 by decide +kernel]
  exact plane273UnusedGen_lb16

end QiushiMatmul.GlobalOrbit.Unused
