import QiushiPlane488GenSources41
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane488GenBound0410 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (410 : Fin 413))) (plane488GenSourceLb (410 : Fin 413)) := by
  rw [show plane488GenSourceBasis (410 : Fin 413) = [258, 128, 64, 32, 18, 10, 6, 1] from rfl,
      show plane488GenSourceLb (410 : Fin 413) = 9 from rfl]
  exact plane488GenSource0410
theorem plane488GenBound0411 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (411 : Fin 413))) (plane488GenSourceLb (411 : Fin 413)) := by
  rw [show plane488GenSourceBasis (411 : Fin 413) = [258, 130, 64, 32, 18, 10, 4, 1] from rfl,
      show plane488GenSourceLb (411 : Fin 413) = 9 from rfl]
  exact plane488GenSource0411
theorem plane488GenBound0412 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (412 : Fin 413))) (plane488GenSourceLb (412 : Fin 413)) := by
  rw [show plane488GenSourceBasis (412 : Fin 413) = [260, 128, 68, 36, 20, 8, 2, 1] from rfl,
      show plane488GenSourceLb (412 : Fin 413) = 9 from rfl]
  exact plane488GenSource0412
end QiushiMatmul
