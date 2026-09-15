import QiushiFrozenRank361Sources08
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane361RankCoverGenBound0080 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (80 : Fin 86))) (plane361RankCoverGenSourceLb (80 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (80 : Fin 86) = [256, 132, 64, 36, 20, 14, 1] from rfl,
      show plane361RankCoverGenSourceLb (80 : Fin 86) = 12 from rfl]
  exact plane361RankCoverGenSource0080
theorem plane361RankCoverGenBound0081 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (81 : Fin 86))) (plane361RankCoverGenSourceLb (81 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (81 : Fin 86) = [256, 132, 64, 36, 20, 12, 2, 1] from rfl,
      show plane361RankCoverGenSourceLb (81 : Fin 86) = 9 from rfl]
  exact plane361RankCoverGenSource0081
theorem plane361RankCoverGenBound0082 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (82 : Fin 86))) (plane361RankCoverGenSourceLb (82 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (82 : Fin 86) = [258, 128, 66, 32, 18, 8, 6, 1] from rfl,
      show plane361RankCoverGenSourceLb (82 : Fin 86) = 9 from rfl]
  exact plane361RankCoverGenSource0082
theorem plane361RankCoverGenBound0083 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (83 : Fin 86))) (plane361RankCoverGenSourceLb (83 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (83 : Fin 86) = [258, 130, 66, 32, 18, 8, 6, 1] from rfl,
      show plane361RankCoverGenSourceLb (83 : Fin 86) = 9 from rfl]
  exact plane361RankCoverGenSource0083
theorem plane361RankCoverGenBound0084 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (84 : Fin 86))) (plane361RankCoverGenSourceLb (84 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (84 : Fin 86) = [256, 128, 66, 32, 18, 10, 6, 1] from rfl,
      show plane361RankCoverGenSourceLb (84 : Fin 86) = 9 from rfl]
  exact plane361RankCoverGenSource0084
theorem plane361RankCoverGenBound0085 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis (85 : Fin 86))) (plane361RankCoverGenSourceLb (85 : Fin 86)) := by
  rw [show plane361RankCoverGenSourceBasis (85 : Fin 86) = [258, 128, 64, 34, 18, 10, 6, 1] from rfl,
      show plane361RankCoverGenSourceLb (85 : Fin 86) = 9 from rfl]
  exact plane361RankCoverGenSource0085
end QiushiMatmul
