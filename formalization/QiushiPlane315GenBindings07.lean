import QiushiPlane315GenSources07
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane315GenBound0070 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (70 : Fin 74))) (plane315GenSourceLb (70 : Fin 74)) := by
  rw [show plane315GenSourceBasis (70 : Fin 74) = [258, 130, 66, 34, 16, 10, 6, 1] from rfl,
      show plane315GenSourceLb (70 : Fin 74) = 9 from rfl]
  exact plane315GenSource0070
theorem plane315GenBound0071 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (71 : Fin 74))) (plane315GenSourceLb (71 : Fin 74)) := by
  rw [show plane315GenSourceBasis (71 : Fin 74) = [256, 130, 66, 34, 18, 10, 4, 1] from rfl,
      show plane315GenSourceLb (71 : Fin 74) = 9 from rfl]
  exact plane315GenSource0071
theorem plane315GenBound0072 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (72 : Fin 74))) (plane315GenSourceLb (72 : Fin 74)) := by
  rw [show plane315GenSourceBasis (72 : Fin 74) = [260, 132, 68, 36, 20, 8, 2, 1] from rfl,
      show plane315GenSourceLb (72 : Fin 74) = 9 from rfl]
  exact plane315GenSource0072
theorem plane315GenBound0073 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (73 : Fin 74))) (plane315GenSourceLb (73 : Fin 74)) := by
  rw [show plane315GenSourceBasis (73 : Fin 74) = [260, 128, 64, 32, 16, 8, 2, 1] from rfl,
      show plane315GenSourceLb (73 : Fin 74) = 3 from rfl]
  exact plane315GenSource0073
end QiushiMatmul
