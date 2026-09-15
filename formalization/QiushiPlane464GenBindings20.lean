import QiushiPlane464GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane464GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane464GenSourceBasis (200 : Fin 202))) (plane464GenSourceLb (200 : Fin 202)) := by
  rw [show plane464GenSourceBasis (200 : Fin 202) = [260, 132, 68, 36, 20, 8, 2, 1] from rfl,
      show plane464GenSourceLb (200 : Fin 202) = 9 from rfl]
  exact plane464GenSource0200
theorem plane464GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane464GenSourceBasis (201 : Fin 202))) (plane464GenSourceLb (201 : Fin 202)) := by
  rw [show plane464GenSourceBasis (201 : Fin 202) = [256, 128, 68, 32, 20, 8, 2, 1] from rfl,
      show plane464GenSourceLb (201 : Fin 202) = 9 from rfl]
  exact plane464GenSource0201
end QiushiMatmul
