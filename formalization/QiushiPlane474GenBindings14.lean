import QiushiPlane474GenSources14
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane474GenBound0140 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (140 : Fin 146))) (plane474GenSourceLb (140 : Fin 146)) := by
  rw [show plane474GenSourceBasis (140 : Fin 146) = [256, 129, 64, 33, 17, 8, 5, 2] from rfl,
      show plane474GenSourceLb (140 : Fin 146) = 9 from rfl]
  exact plane474GenSource0140
theorem plane474GenBound0141 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (141 : Fin 146))) (plane474GenSourceLb (141 : Fin 146)) := by
  rw [show plane474GenSourceBasis (141 : Fin 146) = [257, 129, 64, 32, 17, 8, 5, 2] from rfl,
      show plane474GenSourceLb (141 : Fin 146) = 9 from rfl]
  exact plane474GenSource0141
theorem plane474GenBound0142 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (142 : Fin 146))) (plane474GenSourceLb (142 : Fin 146)) := by
  rw [show plane474GenSourceBasis (142 : Fin 146) = [256, 129, 65, 33, 16, 8, 5, 2] from rfl,
      show plane474GenSourceLb (142 : Fin 146) = 9 from rfl]
  exact plane474GenSource0142
theorem plane474GenBound0143 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (143 : Fin 146))) (plane474GenSourceLb (143 : Fin 146)) := by
  rw [show plane474GenSourceBasis (143 : Fin 146) = [258, 128, 64, 34, 18, 10, 6, 1] from rfl,
      show plane474GenSourceLb (143 : Fin 146) = 9 from rfl]
  exact plane474GenSource0143
theorem plane474GenBound0144 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (144 : Fin 146))) (plane474GenSourceLb (144 : Fin 146)) := by
  rw [show plane474GenSourceBasis (144 : Fin 146) = [258, 128, 66, 32, 18, 10, 4, 1] from rfl,
      show plane474GenSourceLb (144 : Fin 146) = 9 from rfl]
  exact plane474GenSource0144
theorem plane474GenBound0145 :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis (145 : Fin 146))) (plane474GenSourceLb (145 : Fin 146)) := by
  rw [show plane474GenSourceBasis (145 : Fin 146) = [258, 130, 64, 32, 16, 10, 4, 1] from rfl,
      show plane474GenSourceLb (145 : Fin 146) = 9 from rfl]
  exact plane474GenSource0145
end QiushiMatmul
