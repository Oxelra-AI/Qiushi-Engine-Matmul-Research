import QiushiPlane468GenSources25
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane468GenBound0250 :
    QuotientRankAtLeast (spanCodes (plane468GenSourceBasis (250 : Fin 253))) (plane468GenSourceLb (250 : Fin 253)) := by
  rw [show plane468GenSourceBasis (250 : Fin 253) = [257, 129, 64, 32, 17, 9, 5, 3] from rfl,
      show plane468GenSourceLb (250 : Fin 253) = 9 from rfl]
  exact plane468GenSource0250
theorem plane468GenBound0251 :
    QuotientRankAtLeast (spanCodes (plane468GenSourceBasis (251 : Fin 253))) (plane468GenSourceLb (251 : Fin 253)) := by
  rw [show plane468GenSourceBasis (251 : Fin 253) = [256, 130, 66, 32, 16, 10, 6, 1] from rfl,
      show plane468GenSourceLb (251 : Fin 253) = 9 from rfl]
  exact plane468GenSource0251
theorem plane468GenBound0252 :
    QuotientRankAtLeast (spanCodes (plane468GenSourceBasis (252 : Fin 253))) (plane468GenSourceLb (252 : Fin 253)) := by
  rw [show plane468GenSourceBasis (252 : Fin 253) = [258, 128, 64, 32, 16, 10, 4, 1] from rfl,
      show plane468GenSourceLb (252 : Fin 253) = 9 from rfl]
  exact plane468GenSource0252
end QiushiMatmul
