import QiushiFrozenRank368Sources02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane368RankCoverGenBound0020 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis (20 : Fin 25))) (plane368RankCoverGenSourceLb (20 : Fin 25)) := by
  rw [show plane368RankCoverGenSourceBasis (20 : Fin 25) = [268, 128, 78, 32, 20, 1] from rfl,
      show plane368RankCoverGenSourceLb (20 : Fin 25) = 15 from rfl]
  exact plane368RankCoverGenSource0020
theorem plane368RankCoverGenBound0021 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis (21 : Fin 25))) (plane368RankCoverGenSourceLb (21 : Fin 25)) := by
  rw [show plane368RankCoverGenSourceBasis (21 : Fin 25) = [264, 132, 72, 36, 20, 2, 1] from rfl,
      show plane368RankCoverGenSourceLb (21 : Fin 25) = 12 from rfl]
  exact plane368RankCoverGenSource0021
theorem plane368RankCoverGenBound0022 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis (22 : Fin 25))) (plane368RankCoverGenSourceLb (22 : Fin 25)) := by
  rw [show plane368RankCoverGenSourceBasis (22 : Fin 25) = [266, 138, 72, 42, 16, 4, 1] from rfl,
      show plane368RankCoverGenSourceLb (22 : Fin 25) = 12 from rfl]
  exact plane368RankCoverGenSource0022
theorem plane368RankCoverGenBound0023 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis (23 : Fin 25))) (plane368RankCoverGenSourceLb (23 : Fin 25)) := by
  rw [show plane368RankCoverGenSourceBasis (23 : Fin 25) = [322, 128, 32, 18, 10, 6, 1] from rfl,
      show plane368RankCoverGenSourceLb (23 : Fin 25) = 12 from rfl]
  exact plane368RankCoverGenSource0023
theorem plane368RankCoverGenBound0024 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis (24 : Fin 25))) (plane368RankCoverGenSourceLb (24 : Fin 25)) := by
  rw [show plane368RankCoverGenSourceBasis (24 : Fin 25) = [262, 130, 68, 34, 20, 10, 1] from rfl,
      show plane368RankCoverGenSourceLb (24 : Fin 25) = 14 from rfl]
  exact plane368RankCoverGenSource0024
end QiushiMatmul
