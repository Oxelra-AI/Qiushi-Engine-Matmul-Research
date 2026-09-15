import QiushiPlane488GenSources10
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane488GenBound0100 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (100 : Fin 413))) (plane488GenSourceLb (100 : Fin 413)) := by
  rw [show plane488GenSourceBasis (100 : Fin 413) = [288, 96, 10] from rfl,
      show plane488GenSourceLb (100 : Fin 413) = 17 from rfl]
  exact plane488GenSource0100
theorem plane488GenBound0101 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (101 : Fin 413))) (plane488GenSourceLb (101 : Fin 413)) := by
  rw [show plane488GenSourceBasis (101 : Fin 413) = [256, 66, 34, 10] from rfl,
      show plane488GenSourceLb (101 : Fin 413) = 17 from rfl]
  exact plane488GenSource0101
theorem plane488GenBound0102 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (102 : Fin 413))) (plane488GenSourceLb (102 : Fin 413)) := by
  rw [show plane488GenSourceBasis (102 : Fin 413) = [258, 64, 32, 10] from rfl,
      show plane488GenSourceLb (102 : Fin 413) = 17 from rfl]
  exact plane488GenSource0102
theorem plane488GenBound0103 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (103 : Fin 413))) (plane488GenSourceLb (103 : Fin 413)) := by
  rw [show plane488GenSourceBasis (103 : Fin 413) = [292, 96, 17, 10] from rfl,
      show plane488GenSourceLb (103 : Fin 413) = 17 from rfl]
  exact plane488GenSource0103
theorem plane488GenBound0104 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (104 : Fin 413))) (plane488GenSourceLb (104 : Fin 413)) := by
  rw [show plane488GenSourceBasis (104 : Fin 413) = [272, 144, 96, 10] from rfl,
      show plane488GenSourceLb (104 : Fin 413) = 17 from rfl]
  exact plane488GenSource0104
theorem plane488GenBound0105 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (105 : Fin 413))) (plane488GenSourceLb (105 : Fin 413)) := by
  rw [show plane488GenSourceBasis (105 : Fin 413) = [308, 178, 96, 10] from rfl,
      show plane488GenSourceLb (105 : Fin 413) = 17 from rfl]
  exact plane488GenSource0105
theorem plane488GenBound0106 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (106 : Fin 413))) (plane488GenSourceLb (106 : Fin 413)) := by
  rw [show plane488GenSourceBasis (106 : Fin 413) = [384, 96, 16, 10] from rfl,
      show plane488GenSourceLb (106 : Fin 413) = 17 from rfl]
  exact plane488GenSource0106
theorem plane488GenBound0107 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (107 : Fin 413))) (plane488GenSourceLb (107 : Fin 413)) := by
  rw [show plane488GenSourceBasis (107 : Fin 413) = [274, 128, 96, 10] from rfl,
      show plane488GenSourceLb (107 : Fin 413) = 17 from rfl]
  exact plane488GenSource0107
theorem plane488GenBound0108 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (108 : Fin 413))) (plane488GenSourceLb (108 : Fin 413)) := by
  rw [show plane488GenSourceBasis (108 : Fin 413) = [386, 96, 16, 10] from rfl,
      show plane488GenSourceLb (108 : Fin 413) = 17 from rfl]
  exact plane488GenSource0108
theorem plane488GenBound0109 :
    QuotientRankAtLeast (spanCodes (plane488GenSourceBasis (109 : Fin 413))) (plane488GenSourceLb (109 : Fin 413)) := by
  rw [show plane488GenSourceBasis (109 : Fin 413) = [309, 160, 96, 10] from rfl,
      show plane488GenSourceLb (109 : Fin 413) = 17 from rfl]
  exact plane488GenSource0109
end QiushiMatmul
