import QiushiPlane315GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane315GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (0 : Fin 74))) (plane315GenSourceLb (0 : Fin 74)) := by
  rw [show plane315GenSourceBasis (0 : Fin 74) = [260, 160, 70, 10, 1] from rfl,
      show plane315GenSourceLb (0 : Fin 74) = 16 from rfl]
  exact plane315GenSource0000
theorem plane315GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (1 : Fin 74))) (plane315GenSourceLb (1 : Fin 74)) := by
  rw [show plane315GenSourceBasis (1 : Fin 74) = [260, 160, 116, 10, 1] from rfl,
      show plane315GenSourceLb (1 : Fin 74) = 16 from rfl]
  exact plane315GenSource0001
theorem plane315GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (2 : Fin 74))) (plane315GenSourceLb (2 : Fin 74)) := by
  rw [show plane315GenSourceBasis (2 : Fin 74) = [260, 160, 118, 10, 1] from rfl,
      show plane315GenSourceLb (2 : Fin 74) = 16 from rfl]
  exact plane315GenSource0002
theorem plane315GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (3 : Fin 74))) (plane315GenSourceLb (3 : Fin 74)) := by
  rw [show plane315GenSourceBasis (3 : Fin 74) = [260, 144, 48, 10, 1] from rfl,
      show plane315GenSourceLb (3 : Fin 74) = 15 from rfl]
  exact plane315GenSource0003
theorem plane315GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (4 : Fin 74))) (plane315GenSourceLb (4 : Fin 74)) := by
  rw [show plane315GenSourceBasis (4 : Fin 74) = [260, 146, 50, 10, 1] from rfl,
      show plane315GenSourceLb (4 : Fin 74) = 15 from rfl]
  exact plane315GenSource0004
theorem plane315GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (5 : Fin 74))) (plane315GenSourceLb (5 : Fin 74)) := by
  rw [show plane315GenSourceBasis (5 : Fin 74) = [256, 160, 64, 10, 4, 1] from rfl,
      show plane315GenSourceLb (5 : Fin 74) = 15 from rfl]
  exact plane315GenSource0005
theorem plane315GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (6 : Fin 74))) (plane315GenSourceLb (6 : Fin 74)) := by
  rw [show plane315GenSourceBasis (6 : Fin 74) = [258, 160, 64, 10, 6, 1] from rfl,
      show plane315GenSourceLb (6 : Fin 74) = 15 from rfl]
  exact plane315GenSource0006
theorem plane315GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (7 : Fin 74))) (plane315GenSourceLb (7 : Fin 74)) := by
  rw [show plane315GenSourceBasis (7 : Fin 74) = [256, 160, 66, 10, 4, 1] from rfl,
      show plane315GenSourceLb (7 : Fin 74) = 15 from rfl]
  exact plane315GenSource0007
theorem plane315GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (8 : Fin 74))) (plane315GenSourceLb (8 : Fin 74)) := by
  rw [show plane315GenSourceBasis (8 : Fin 74) = [260, 160, 68, 20, 10, 1] from rfl,
      show plane315GenSourceLb (8 : Fin 74) = 15 from rfl]
  exact plane315GenSource0008
theorem plane315GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis (9 : Fin 74))) (plane315GenSourceLb (9 : Fin 74)) := by
  rw [show plane315GenSourceBasis (9 : Fin 74) = [260, 160, 68, 16, 10, 1] from rfl,
      show plane315GenSourceLb (9 : Fin 74) = 15 from rfl]
  exact plane315GenSource0009
end QiushiMatmul
