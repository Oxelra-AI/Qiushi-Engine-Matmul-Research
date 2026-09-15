import QiushiPlane461GenSources15
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane461GenBound0150 :
    QuotientRankAtLeast (spanCodes (plane461GenSourceBasis (150 : Fin 151))) (plane461GenSourceLb (150 : Fin 151)) := by
  rw [show plane461GenSourceBasis (150 : Fin 151) = [258, 130, 64, 32, 16, 10, 4, 1] from rfl,
      show plane461GenSourceLb (150 : Fin 151) = 9 from rfl]
  exact plane461GenSource0150
end QiushiMatmul
