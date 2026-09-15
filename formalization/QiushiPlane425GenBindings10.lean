import QiushiPlane425GenSources10
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane425GenBound0100 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (100 : Fin 202))) (plane425GenSourceLb (100 : Fin 202)) := by
  rw [show plane425GenSourceBasis (100 : Fin 202) = [256, 100, 8, 2, 1] from rfl,
      show plane425GenSourceLb (100 : Fin 202) = 14 from rfl]
  exact plane425GenSource0100
theorem plane425GenBound0101 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (101 : Fin 202))) (plane425GenSourceLb (101 : Fin 202)) := by
  rw [show plane425GenSourceBasis (101 : Fin 202) = [258, 144, 80, 10, 6, 1] from rfl,
      show plane425GenSourceLb (101 : Fin 202) = 14 from rfl]
  exact plane425GenSource0101
theorem plane425GenBound0102 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (102 : Fin 202))) (plane425GenSourceLb (102 : Fin 202)) := by
  rw [show plane425GenSourceBasis (102 : Fin 202) = [258, 128, 80, 10, 6, 1] from rfl,
      show plane425GenSourceLb (102 : Fin 202) = 14 from rfl]
  exact plane425GenSource0102
theorem plane425GenBound0103 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (103 : Fin 202))) (plane425GenSourceLb (103 : Fin 202)) := by
  rw [show plane425GenSourceBasis (103 : Fin 202) = [258, 144, 84, 36, 10, 1] from rfl,
      show plane425GenSourceLb (103 : Fin 202) = 14 from rfl]
  exact plane425GenSource0103
theorem plane425GenBound0104 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (104 : Fin 202))) (plane425GenSourceLb (104 : Fin 202)) := by
  rw [show plane425GenSourceBasis (104 : Fin 202) = [258, 128, 84, 52, 10, 1] from rfl,
      show plane425GenSourceLb (104 : Fin 202) = 14 from rfl]
  exact plane425GenSource0104
theorem plane425GenBound0105 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (105 : Fin 202))) (plane425GenSourceLb (105 : Fin 202)) := by
  rw [show plane425GenSourceBasis (105 : Fin 202) = [258, 132, 86, 48, 10, 1] from rfl,
      show plane425GenSourceLb (105 : Fin 202) = 14 from rfl]
  exact plane425GenSource0105
theorem plane425GenBound0106 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (106 : Fin 202))) (plane425GenSourceLb (106 : Fin 202)) := by
  rw [show plane425GenSourceBasis (106 : Fin 202) = [258, 128, 86, 52, 10, 1] from rfl,
      show plane425GenSourceLb (106 : Fin 202) = 14 from rfl]
  exact plane425GenSource0106
theorem plane425GenBound0107 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (107 : Fin 202))) (plane425GenSourceLb (107 : Fin 202)) := by
  rw [show plane425GenSourceBasis (107 : Fin 202) = [258, 128, 86, 50, 10, 1] from rfl,
      show plane425GenSourceLb (107 : Fin 202) = 14 from rfl]
  exact plane425GenSource0107
theorem plane425GenBound0108 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (108 : Fin 202))) (plane425GenSourceLb (108 : Fin 202)) := by
  rw [show plane425GenSourceBasis (108 : Fin 202) = [258, 150, 84, 36, 10, 1] from rfl,
      show plane425GenSourceLb (108 : Fin 202) = 14 from rfl]
  exact plane425GenSource0108
theorem plane425GenBound0109 :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis (109 : Fin 202))) (plane425GenSourceLb (109 : Fin 202)) := by
  rw [show plane425GenSourceBasis (109 : Fin 202) = [258, 134, 84, 52, 10, 1] from rfl,
      show plane425GenSourceLb (109 : Fin 202) = 14 from rfl]
  exact plane425GenSource0109
end QiushiMatmul
