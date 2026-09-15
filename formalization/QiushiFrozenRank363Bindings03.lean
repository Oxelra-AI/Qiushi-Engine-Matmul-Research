import QiushiFrozenRank363Sources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane363RankCoverGenBound0030 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenSourceBasis (30 : Fin 33))) (plane363RankCoverGenSourceLb (30 : Fin 33)) := by
  rw [show plane363RankCoverGenSourceBasis (30 : Fin 33) = [260, 128, 68, 32, 20, 8, 2, 1] from rfl,
      show plane363RankCoverGenSourceLb (30 : Fin 33) = 9 from rfl]
  exact plane363RankCoverGenSource0030
theorem plane363RankCoverGenBound0031 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenSourceBasis (31 : Fin 33))) (plane363RankCoverGenSourceLb (31 : Fin 33)) := by
  rw [show plane363RankCoverGenSourceBasis (31 : Fin 33) = [258, 130, 64, 34, 16, 10, 4, 1] from rfl,
      show plane363RankCoverGenSourceLb (31 : Fin 33) = 9 from rfl]
  exact plane363RankCoverGenSource0031
theorem plane363RankCoverGenBound0032 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenSourceBasis (32 : Fin 33))) (plane363RankCoverGenSourceLb (32 : Fin 33)) := by
  rw [show plane363RankCoverGenSourceBasis (32 : Fin 33) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane363RankCoverGenSourceLb (32 : Fin 33) = 9 from rfl]
  exact plane363RankCoverGenSource0032
end QiushiMatmul
