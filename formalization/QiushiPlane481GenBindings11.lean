import QiushiPlane481GenSources11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane481GenBound0110 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (110 : Fin 116))) (plane481GenSourceLb (110 : Fin 116)) := by
  rw [show plane481GenSourceBasis (110 : Fin 116) = [362, 130, 16, 4, 1] from rfl,
      show plane481GenSourceLb (110 : Fin 116) = 14 from rfl]
  exact plane481GenSource0110
theorem plane481GenBound0111 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (111 : Fin 116))) (plane481GenSourceLb (111 : Fin 116)) := by
  rw [show plane481GenSourceBasis (111 : Fin 116) = [260, 128, 70, 38, 20, 10, 1] from rfl,
      show plane481GenSourceLb (111 : Fin 116) = 14 from rfl]
  exact plane481GenSource0111
theorem plane481GenBound0112 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (112 : Fin 116))) (plane481GenSourceLb (112 : Fin 116)) := by
  rw [show plane481GenSourceBasis (112 : Fin 116) = [128, 66, 32, 18, 8, 6, 1] from rfl,
      show plane481GenSourceLb (112 : Fin 116) = 12 from rfl]
  exact plane481GenSource0112
theorem plane481GenBound0113 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (113 : Fin 116))) (plane481GenSourceLb (113 : Fin 116)) := by
  rw [show plane481GenSourceBasis (113 : Fin 116) = [258, 160, 96, 18, 10, 6, 1] from rfl,
      show plane481GenSourceLb (113 : Fin 116) = 12 from rfl]
  exact plane481GenSource0113
theorem plane481GenBound0114 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (114 : Fin 116))) (plane481GenSourceLb (114 : Fin 116)) := by
  rw [show plane481GenSourceBasis (114 : Fin 116) = [264, 128, 74, 32, 16, 4, 1] from rfl,
      show plane481GenSourceLb (114 : Fin 116) = 12 from rfl]
  exact plane481GenSource0114
theorem plane481GenBound0115 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (115 : Fin 116))) (plane481GenSourceLb (115 : Fin 116)) := by
  rw [show plane481GenSourceBasis (115 : Fin 116) = [260, 130, 66, 32, 20, 12, 1] from rfl,
      show plane481GenSourceLb (115 : Fin 116) = 12 from rfl]
  exact plane481GenSource0115
end QiushiMatmul
