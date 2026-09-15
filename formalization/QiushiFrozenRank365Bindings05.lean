import QiushiFrozenRank365Sources05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane365RankCoverGenBound0050 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenSourceBasis (50 : Fin 52))) (plane365RankCoverGenSourceLb (50 : Fin 52)) := by
  rw [show plane365RankCoverGenSourceBasis (50 : Fin 52) = [256, 128, 66, 32, 18, 10, 6, 1] from rfl,
      show plane365RankCoverGenSourceLb (50 : Fin 52) = 9 from rfl]
  exact plane365RankCoverGenSource0050
theorem plane365RankCoverGenBound0051 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenSourceBasis (51 : Fin 52))) (plane365RankCoverGenSourceLb (51 : Fin 52)) := by
  rw [show plane365RankCoverGenSourceBasis (51 : Fin 52) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane365RankCoverGenSourceLb (51 : Fin 52) = 9 from rfl]
  exact plane365RankCoverGenSource0051
end QiushiMatmul
