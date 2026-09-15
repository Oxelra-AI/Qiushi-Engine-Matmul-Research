import QiushiPlane425GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane425GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (200 : Fin 202))) (plane425GenSourceLb (200 : Fin 202)) := by
  rw [show plane425GenSourceBasis (200 : Fin 202) = [256, 144, 80, 32, 8, 4, 2, 1] from rfl,
      show plane425GenSourceLb (200 : Fin 202) = 6 from rfl]
  exact plane425GenSource0200
theorem plane425GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (201 : Fin 202))) (plane425GenSourceLb (201 : Fin 202)) := by
  rw [show plane425GenSourceBasis (201 : Fin 202) = [256, 144, 80, 48, 8, 4, 2, 1] from rfl,
      show plane425GenSourceLb (201 : Fin 202) = 6 from rfl]
  exact plane425GenSource0201
end QiushiMatmul
