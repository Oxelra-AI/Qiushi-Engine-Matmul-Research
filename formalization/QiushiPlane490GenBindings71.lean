import QiushiPlane490GenSources71
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane490GenBound0710 :
    QuotientRankAtLeast (spanCodes (plane490GenSourceBasis (710 : Fin 713))) (plane490GenSourceLb (710 : Fin 713)) := by
  rw [show plane490GenSourceBasis (710 : Fin 713) = [256, 128, 66, 34, 18, 10, 4, 1] from rfl,
      show plane490GenSourceLb (710 : Fin 713) = 9 from rfl]
  exact plane490GenSource0710
theorem plane490GenBound0711 :
    QuotientRankAtLeast (spanCodes (plane490GenSourceBasis (711 : Fin 713))) (plane490GenSourceLb (711 : Fin 713)) := by
  rw [show plane490GenSourceBasis (711 : Fin 713) = [260, 128, 68, 36, 20, 8, 2, 1] from rfl,
      show plane490GenSourceLb (711 : Fin 713) = 9 from rfl]
  exact plane490GenSource0711
theorem plane490GenBound0712 :
    QuotientRankAtLeast (spanCodes (plane490GenSourceBasis (712 : Fin 713))) (plane490GenSourceLb (712 : Fin 713)) := by
  rw [show plane490GenSourceBasis (712 : Fin 713) = [260, 132, 68, 32, 20, 8, 2, 1] from rfl,
      show plane490GenSourceLb (712 : Fin 713) = 9 from rfl]
  exact plane490GenSource0712
end QiushiMatmul
