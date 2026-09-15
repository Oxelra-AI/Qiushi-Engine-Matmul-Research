import QiushiPlane336GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane336GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (10 : Fin 34))) (plane336GenSourceLb (10 : Fin 34)) := by
  rw [show plane336GenSourceBasis (10 : Fin 34) = [256, 168, 98, 16, 1] from rfl,
      show plane336GenSourceLb (10 : Fin 34) = 15 from rfl]
  exact plane336GenSource0010
theorem plane336GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (11 : Fin 34))) (plane336GenSourceLb (11 : Fin 34)) := by
  rw [show plane336GenSourceBasis (11 : Fin 34) = [256, 172, 98, 16, 1] from rfl,
      show plane336GenSourceLb (11 : Fin 34) = 15 from rfl]
  exact plane336GenSource0011
theorem plane336GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (12 : Fin 34))) (plane336GenSourceLb (12 : Fin 34)) := by
  rw [show plane336GenSourceBasis (12 : Fin 34) = [256, 174, 98, 16, 1] from rfl,
      show plane336GenSourceLb (12 : Fin 34) = 15 from rfl]
  exact plane336GenSource0012
theorem plane336GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (13 : Fin 34))) (plane336GenSourceLb (13 : Fin 34)) := by
  rw [show plane336GenSourceBasis (13 : Fin 34) = [256, 66, 32, 16, 1] from rfl,
      show plane336GenSourceLb (13 : Fin 34) = 14 from rfl]
  exact plane336GenSource0013
theorem plane336GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (14 : Fin 34))) (plane336GenSourceLb (14 : Fin 34)) := by
  rw [show plane336GenSourceBasis (14 : Fin 34) = [256, 64, 34, 16, 1] from rfl,
      show plane336GenSourceLb (14 : Fin 34) = 14 from rfl]
  exact plane336GenSource0014
theorem plane336GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (15 : Fin 34))) (plane336GenSourceLb (15 : Fin 34)) := by
  rw [show plane336GenSourceBasis (15 : Fin 34) = [256, 72, 42, 16, 1] from rfl,
      show plane336GenSourceLb (15 : Fin 34) = 14 from rfl]
  exact plane336GenSource0015
theorem plane336GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (16 : Fin 34))) (plane336GenSourceLb (16 : Fin 34)) := by
  rw [show plane336GenSourceBasis (16 : Fin 34) = [256, 98, 16, 8, 4, 1] from rfl,
      show plane336GenSourceLb (16 : Fin 34) = 12 from rfl]
  exact plane336GenSource0016
theorem plane336GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (17 : Fin 34))) (plane336GenSourceLb (17 : Fin 34)) := by
  rw [show plane336GenSourceBasis (17 : Fin 34) = [256, 128, 98, 16, 4, 1] from rfl,
      show plane336GenSourceLb (17 : Fin 34) = 12 from rfl]
  exact plane336GenSource0017
theorem plane336GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (18 : Fin 34))) (plane336GenSourceLb (18 : Fin 34)) := by
  rw [show plane336GenSourceBasis (18 : Fin 34) = [256, 128, 98, 16, 8, 1] from rfl,
      show plane336GenSourceLb (18 : Fin 34) = 12 from rfl]
  exact plane336GenSource0018
theorem plane336GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (19 : Fin 34))) (plane336GenSourceLb (19 : Fin 34)) := by
  rw [show plane336GenSourceBasis (19 : Fin 34) = [256, 132, 96, 16, 8, 2, 1] from rfl,
      show plane336GenSourceLb (19 : Fin 34) = 12 from rfl]
  exact plane336GenSource0019
end QiushiMatmul
