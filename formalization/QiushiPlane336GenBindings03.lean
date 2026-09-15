import QiushiPlane336GenSources03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane336GenBound0030 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (30 : Fin 34))) (plane336GenSourceLb (30 : Fin 34)) := by
  rw [show plane336GenSourceBasis (30 : Fin 34) = [256, 128, 64, 34, 16, 8, 1] from rfl,
      show plane336GenSourceLb (30 : Fin 34) = 9 from rfl]
  exact plane336GenSource0030
theorem plane336GenBound0031 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (31 : Fin 34))) (plane336GenSourceLb (31 : Fin 34)) := by
  rw [show plane336GenSourceBasis (31 : Fin 34) = [256, 130, 64, 34, 16, 10, 6, 1] from rfl,
      show plane336GenSourceLb (31 : Fin 34) = 9 from rfl]
  exact plane336GenSource0031
theorem plane336GenBound0032 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (32 : Fin 34))) (plane336GenSourceLb (32 : Fin 34)) := by
  rw [show plane336GenSourceBasis (32 : Fin 34) = [256, 130, 66, 32, 16, 10, 6, 1] from rfl,
      show plane336GenSourceLb (32 : Fin 34) = 9 from rfl]
  exact plane336GenSource0032
theorem plane336GenBound0033 :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis (33 : Fin 34))) (plane336GenSourceLb (33 : Fin 34)) := by
  rw [show plane336GenSourceBasis (33 : Fin 34) = [256, 132, 68, 36, 16, 12, 2, 1] from rfl,
      show plane336GenSourceLb (33 : Fin 34) = 9 from rfl]
  exact plane336GenSource0033
end QiushiMatmul
