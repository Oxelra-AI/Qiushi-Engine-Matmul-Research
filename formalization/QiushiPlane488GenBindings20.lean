import QiushiPlane488GenSources20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane488GenBound0200 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (200 : Fin 413))) (plane488GenSourceLb (200 : Fin 413)) := by
  rw [show plane488GenSourceBasis (200 : Fin 413) = [256, 128, 65, 33, 10, 4] from rfl,
      show plane488GenSourceLb (200 : Fin 413) = 15 from rfl]
  exact plane488GenSource0200
theorem plane488GenBound0201 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (201 : Fin 413))) (plane488GenSourceLb (201 : Fin 413)) := by
  rw [show plane488GenSourceBasis (201 : Fin 413) = [273, 130, 81, 49, 10, 7] from rfl,
      show plane488GenSourceLb (201 : Fin 413) = 15 from rfl]
  exact plane488GenSource0201
theorem plane488GenBound0202 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (202 : Fin 413))) (plane488GenSourceLb (202 : Fin 413)) := by
  rw [show plane488GenSourceBasis (202 : Fin 413) = [256, 160, 96, 10, 4, 1] from rfl,
      show plane488GenSourceLb (202 : Fin 413) = 15 from rfl]
  exact plane488GenSource0202
theorem plane488GenBound0203 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (203 : Fin 413))) (plane488GenSourceLb (203 : Fin 413)) := by
  rw [show plane488GenSourceBasis (203 : Fin 413) = [402, 80, 48, 10, 6, 1] from rfl,
      show plane488GenSourceLb (203 : Fin 413) = 15 from rfl]
  exact plane488GenSource0203
theorem plane488GenBound0204 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (204 : Fin 413))) (plane488GenSourceLb (204 : Fin 413)) := by
  rw [show plane488GenSourceBasis (204 : Fin 413) = [257, 147, 80, 48, 10, 4] from rfl,
      show plane488GenSourceLb (204 : Fin 413) = 15 from rfl]
  exact plane488GenSource0204
theorem plane488GenBound0205 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (205 : Fin 413))) (plane488GenSourceLb (205 : Fin 413)) := by
  rw [show plane488GenSourceBasis (205 : Fin 413) = [257, 131, 65, 33, 10, 5] from rfl,
      show plane488GenSourceLb (205 : Fin 413) = 15 from rfl]
  exact plane488GenSource0205
theorem plane488GenBound0206 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (206 : Fin 413))) (plane488GenSourceLb (206 : Fin 413)) := by
  rw [show plane488GenSourceBasis (206 : Fin 413) = [277, 144, 65, 33, 8, 2] from rfl,
      show plane488GenSourceLb (206 : Fin 413) = 15 from rfl]
  exact plane488GenSource0206
theorem plane488GenBound0207 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (207 : Fin 413))) (plane488GenSourceLb (207 : Fin 413)) := by
  rw [show plane488GenSourceBasis (207 : Fin 413) = [401, 80, 48, 8, 5, 2] from rfl,
      show plane488GenSourceLb (207 : Fin 413) = 15 from rfl]
  exact plane488GenSource0207
theorem plane488GenBound0208 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (208 : Fin 413))) (plane488GenSourceLb (208 : Fin 413)) := by
  rw [show plane488GenSourceBasis (208 : Fin 413) = [274, 146, 71, 39, 10] from rfl,
      show plane488GenSourceLb (208 : Fin 413) = 15 from rfl]
  exact plane488GenSource0208
theorem plane488GenBound0209 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (209 : Fin 413))) (plane488GenSourceLb (209 : Fin 413)) := by
  rw [show plane488GenSourceBasis (209 : Fin 413) = [272, 145, 64, 32, 10, 6] from rfl,
      show plane488GenSourceLb (209 : Fin 413) = 15 from rfl]
  exact plane488GenSource0209
end QiushiMatmul
