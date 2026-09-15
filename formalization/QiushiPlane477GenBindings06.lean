import QiushiPlane477GenSources06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane477GenBound0060 :
    QuotientRankAtLeast (spanCodes (plane477GenSourceBasis (60 : Fin 63))) (plane477GenSourceLb (60 : Fin 63)) := by
  rw [show plane477GenSourceBasis (60 : Fin 63) = [286, 158, 84, 61] from rfl,
      show plane477GenSourceLb (60 : Fin 63) = 17 from rfl]
  exact plane477GenSource0060
theorem plane477GenBound0061 :
    QuotientRankAtLeast (spanCodes (plane477GenSourceBasis (61 : Fin 63))) (plane477GenSourceLb (61 : Fin 63)) := by
  rw [show plane477GenSourceBasis (61 : Fin 63) = [286, 157, 84, 62] from rfl,
      show plane477GenSourceLb (61 : Fin 63) = 17 from rfl]
  exact plane477GenSource0061
theorem plane477GenBound0062 :
    QuotientRankAtLeast (spanCodes (plane477GenSourceBasis (62 : Fin 63))) (plane477GenSourceLb (62 : Fin 63)) := by
  rw [show plane477GenSourceBasis (62 : Fin 63) = [286, 156, 84, 63] from rfl,
      show plane477GenSourceLb (62 : Fin 63) = 17 from rfl]
  exact plane477GenSource0062
end QiushiMatmul
