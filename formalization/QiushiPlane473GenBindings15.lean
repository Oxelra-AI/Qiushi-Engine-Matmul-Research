import QiushiPlane473GenSources15
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane473GenBound0150 :
    QuotientRankAtLeast (spanCodes (plane473GenSourceBasis (150 : Fin 153))) (plane473GenSourceLb (150 : Fin 153)) := by
  rw [show plane473GenSourceBasis (150 : Fin 153) = [257, 129, 65, 33, 16, 8, 5, 2] from rfl,
      show plane473GenSourceLb (150 : Fin 153) = 9 from rfl]
  exact plane473GenSource0150
theorem plane473GenBound0151 :
    QuotientRankAtLeast (spanCodes (plane473GenSourceBasis (151 : Fin 153))) (plane473GenSourceLb (151 : Fin 153)) := by
  rw [show plane473GenSourceBasis (151 : Fin 153) = [256, 129, 65, 33, 17, 8, 4, 2] from rfl,
      show plane473GenSourceLb (151 : Fin 153) = 9 from rfl]
  exact plane473GenSource0151
theorem plane473GenBound0152 :
    QuotientRankAtLeast (spanCodes (plane473GenSourceBasis (152 : Fin 153))) (plane473GenSourceLb (152 : Fin 153)) := by
  rw [show plane473GenSourceBasis (152 : Fin 153) = [257, 128, 65, 32, 17, 8, 4, 2] from rfl,
      show plane473GenSourceLb (152 : Fin 153) = 9 from rfl]
  exact plane473GenSource0152
end QiushiMatmul
