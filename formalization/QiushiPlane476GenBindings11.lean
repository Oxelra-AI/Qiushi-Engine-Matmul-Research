import QiushiPlane476GenSources11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane476GenBound0110 :
    QuotientRankAtLeast (spanCodes (plane476GenSourceBasis (110 : Fin 113))) (plane476GenSourceLb (110 : Fin 113)) := by
  rw [show plane476GenSourceBasis (110 : Fin 113) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane476GenSourceLb (110 : Fin 113) = 9 from rfl]
  exact plane476GenSource0110
theorem plane476GenBound0111 :
    QuotientRankAtLeast (spanCodes (plane476GenSourceBasis (111 : Fin 113))) (plane476GenSourceLb (111 : Fin 113)) := by
  rw [show plane476GenSourceBasis (111 : Fin 113) = [258, 130, 66, 34, 16, 10, 6, 1] from rfl,
      show plane476GenSourceLb (111 : Fin 113) = 9 from rfl]
  exact plane476GenSource0111
theorem plane476GenBound0112 :
    QuotientRankAtLeast (spanCodes (plane476GenSourceBasis (112 : Fin 113))) (plane476GenSourceLb (112 : Fin 113)) := by
  rw [show plane476GenSourceBasis (112 : Fin 113) = [256, 132, 68, 36, 20, 8, 2, 1] from rfl,
      show plane476GenSourceLb (112 : Fin 113) = 9 from rfl]
  exact plane476GenSource0112
end QiushiMatmul
