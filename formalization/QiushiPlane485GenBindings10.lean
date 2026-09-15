import QiushiPlane485GenSources10
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane485GenBound0100 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (100 : Fin 421))) (plane485GenSourceLb (100 : Fin 421)) := by
  rw [show plane485GenSourceBasis (100 : Fin 421) = [260, 36, 20, 10] from rfl,
      show plane485GenSourceLb (100 : Fin 421) = 16 from rfl]
  exact plane485GenSource0100
theorem plane485GenBound0101 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (101 : Fin 421))) (plane485GenSourceLb (101 : Fin 421)) := by
  rw [show plane485GenSourceBasis (101 : Fin 421) = [256, 36, 20, 10] from rfl,
      show plane485GenSourceLb (101 : Fin 421) = 16 from rfl]
  exact plane485GenSource0101
theorem plane485GenBound0102 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (102 : Fin 421))) (plane485GenSourceLb (102 : Fin 421)) := by
  rw [show plane485GenSourceBasis (102 : Fin 421) = [288, 16, 10, 4] from rfl,
      show plane485GenSourceLb (102 : Fin 421) = 16 from rfl]
  exact plane485GenSource0102
theorem plane485GenBound0103 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (103 : Fin 421))) (plane485GenSourceLb (103 : Fin 421)) := by
  rw [show plane485GenSourceBasis (103 : Fin 421) = [258, 32, 16, 10, 4] from rfl,
      show plane485GenSourceLb (103 : Fin 421) = 16 from rfl]
  exact plane485GenSource0103
theorem plane485GenBound0104 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (104 : Fin 421))) (plane485GenSourceLb (104 : Fin 421)) := by
  rw [show plane485GenSourceBasis (104 : Fin 421) = [256, 64, 20, 10] from rfl,
      show plane485GenSourceLb (104 : Fin 421) = 16 from rfl]
  exact plane485GenSource0104
theorem plane485GenBound0105 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (105 : Fin 421))) (plane485GenSourceLb (105 : Fin 421)) := by
  rw [show plane485GenSourceBasis (105 : Fin 421) = [260, 65, 20, 10] from rfl,
      show plane485GenSourceLb (105 : Fin 421) = 16 from rfl]
  exact plane485GenSource0105
theorem plane485GenBound0106 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (106 : Fin 421))) (plane485GenSourceLb (106 : Fin 421)) := by
  rw [show plane485GenSourceBasis (106 : Fin 421) = [320, 17, 10, 5] from rfl,
      show plane485GenSourceLb (106 : Fin 421) = 16 from rfl]
  exact plane485GenSource0106
theorem plane485GenBound0107 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (107 : Fin 421))) (plane485GenSourceLb (107 : Fin 421)) := by
  rw [show plane485GenSourceBasis (107 : Fin 421) = [320, 34, 20, 10] from rfl,
      show plane485GenSourceLb (107 : Fin 421) = 16 from rfl]
  exact plane485GenSource0107
theorem plane485GenBound0108 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (108 : Fin 421))) (plane485GenSourceLb (108 : Fin 421)) := by
  rw [show plane485GenSourceBasis (108 : Fin 421) = [325, 34, 20, 10] from rfl,
      show plane485GenSourceLb (108 : Fin 421) = 16 from rfl]
  exact plane485GenSource0108
theorem plane485GenBound0109 :
    QuotientRankAtLeast (spanCodes (plane485GenSourceBasis (109 : Fin 421))) (plane485GenSourceLb (109 : Fin 421)) := by
  rw [show plane485GenSourceBasis (109 : Fin 421) = [262, 65, 32, 20, 10] from rfl,
      show plane485GenSourceLb (109 : Fin 421) = 16 from rfl]
  exact plane485GenSource0109
end QiushiMatmul
