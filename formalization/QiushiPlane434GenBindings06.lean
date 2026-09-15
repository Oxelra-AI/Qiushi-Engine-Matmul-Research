import QiushiPlane434GenSources06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane434GenBound0060 :
    QuotientRankAtLeast (spanCodes (plane434GenSourceBasis (60 : Fin 63))) (plane434GenSourceLb (60 : Fin 63)) := by
  rw [show plane434GenSourceBasis (60 : Fin 63) = [262, 132, 66, 36, 16, 12, 1] from rfl,
      show plane434GenSourceLb (60 : Fin 63) = 12 from rfl]
  exact plane434GenSource0060
theorem plane434GenBound0061 :
    QuotientRankAtLeast (spanCodes (plane434GenSourceBasis (61 : Fin 63))) (plane434GenSourceLb (61 : Fin 63)) := by
  rw [show plane434GenSourceBasis (61 : Fin 63) = [266, 138, 64, 34, 16, 6, 1] from rfl,
      show plane434GenSourceLb (61 : Fin 63) = 12 from rfl]
  exact plane434GenSource0061
theorem plane434GenBound0062 :
    QuotientRankAtLeast (spanCodes (plane434GenSourceBasis (62 : Fin 63))) (plane434GenSourceLb (62 : Fin 63)) := by
  rw [show plane434GenSourceBasis (62 : Fin 63) = [266, 136, 72, 42, 16, 4, 1] from rfl,
      show plane434GenSourceLb (62 : Fin 63) = 12 from rfl]
  exact plane434GenSource0062
end QiushiMatmul
