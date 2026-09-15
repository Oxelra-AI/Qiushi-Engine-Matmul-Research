import QiushiPlane454GenSources17
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane454GenBound0170 :
    QuotientRankAtLeast (spanCodes (plane454GenSourceBasis (170 : Fin 174))) (plane454GenSourceLb (170 : Fin 174)) := by
  rw [show plane454GenSourceBasis (170 : Fin 174) = [256, 130, 66, 34, 18, 10, 6, 1] from rfl,
      show plane454GenSourceLb (170 : Fin 174) = 9 from rfl]
  exact plane454GenSource0170
theorem plane454GenBound0171 :
    QuotientRankAtLeast (spanCodes (plane454GenSourceBasis (171 : Fin 174))) (plane454GenSourceLb (171 : Fin 174)) := by
  rw [show plane454GenSourceBasis (171 : Fin 174) = [258, 128, 66, 34, 18, 10, 6, 1] from rfl,
      show plane454GenSourceLb (171 : Fin 174) = 9 from rfl]
  exact plane454GenSource0171
theorem plane454GenBound0172 :
    QuotientRankAtLeast (spanCodes (plane454GenSourceBasis (172 : Fin 174))) (plane454GenSourceLb (172 : Fin 174)) := by
  rw [show plane454GenSourceBasis (172 : Fin 174) = [256, 128, 66, 34, 16, 10, 4, 1] from rfl,
      show plane454GenSourceLb (172 : Fin 174) = 9 from rfl]
  exact plane454GenSource0172
theorem plane454GenBound0173 :
    QuotientRankAtLeast (spanCodes (plane454GenSourceBasis (173 : Fin 174))) (plane454GenSourceLb (173 : Fin 174)) := by
  rw [show plane454GenSourceBasis (173 : Fin 174) = [258, 128, 64, 32, 16, 10, 4, 1] from rfl,
      show plane454GenSourceLb (173 : Fin 174) = 9 from rfl]
  exact plane454GenSource0173
end QiushiMatmul
