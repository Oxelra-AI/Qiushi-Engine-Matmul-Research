import QiushiFrozenRank362Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane362RankCoverGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenSourceBasis (30 : Fin 31))) (plane362RankCoverGenSourceLb (30 : Fin 31)) := by
  rw [show plane362RankCoverGenSourceBasis (30 : Fin 31) = [260, 128, 68, 32, 20, 12, 2, 1] from rfl,
      show plane362RankCoverGenSourceLb (30 : Fin 31) = 9 from rfl]
  exact plane362RankCoverGenSource0030
end QiushiMatmul
