import FrozenRegistry.Reductions
import QiushiFrozenRank162

namespace QiushiMatmul.FrozenRegistry.ClosedReductions

theorem bound341 : QuotientRankAtLeast (spanCodes [290,100,16,1]) 16 := by
  have h := Reductions.rep341_of_rep162 FrozenRank.rep162
  rw [show frozenWangTable.basis 341 = [290,100,16,1] by decide +kernel,
      show frozenWangTable.lower 341 = 16 by decide +kernel] at h
  exact h

end QiushiMatmul.FrozenRegistry.ClosedReductions
