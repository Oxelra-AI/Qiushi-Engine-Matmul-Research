import QiushiPlane430GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane430GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (0 : Fin 57))) (plane430GenSourceLb (0 : Fin 57)) := by
  rw [show plane430GenSourceBasis (0 : Fin 57) = [66, 38, 16, 12, 1] from rfl,
      show plane430GenSourceLb (0 : Fin 57) = 16 from rfl]
  exact plane430GenSource0000
theorem plane430GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (1 : Fin 57))) (plane430GenSourceLb (1 : Fin 57)) := by
  rw [show plane430GenSourceBasis (1 : Fin 57) = [70, 34, 16, 12, 1] from rfl,
      show plane430GenSourceLb (1 : Fin 57) = 16 from rfl]
  exact plane430GenSource0001
theorem plane430GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (2 : Fin 57))) (plane430GenSourceLb (2 : Fin 57)) := by
  rw [show plane430GenSourceBasis (2 : Fin 57) = [136, 100, 16, 1] from rfl,
      show plane430GenSourceLb (2 : Fin 57) = 16 from rfl]
  exact plane430GenSource0002
theorem plane430GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (3 : Fin 57))) (plane430GenSourceLb (3 : Fin 57)) := by
  rw [show plane430GenSourceBasis (3 : Fin 57) = [138, 100, 16, 1] from rfl,
      show plane430GenSourceLb (3 : Fin 57) = 16 from rfl]
  exact plane430GenSource0003
theorem plane430GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (4 : Fin 57))) (plane430GenSourceLb (4 : Fin 57)) := by
  rw [show plane430GenSourceBasis (4 : Fin 57) = [138, 78, 42, 16, 1] from rfl,
      show plane430GenSourceLb (4 : Fin 57) = 16 from rfl]
  exact plane430GenSource0004
theorem plane430GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (5 : Fin 57))) (plane430GenSourceLb (5 : Fin 57)) := by
  rw [show plane430GenSourceBasis (5 : Fin 57) = [136, 78, 42, 16, 1] from rfl,
      show plane430GenSourceLb (5 : Fin 57) = 16 from rfl]
  exact plane430GenSource0005
theorem plane430GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (6 : Fin 57))) (plane430GenSourceLb (6 : Fin 57)) := by
  rw [show plane430GenSourceBasis (6 : Fin 57) = [138, 70, 34, 16, 1] from rfl,
      show plane430GenSourceLb (6 : Fin 57) = 16 from rfl]
  exact plane430GenSource0006
theorem plane430GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (7 : Fin 57))) (plane430GenSourceLb (7 : Fin 57)) := by
  rw [show plane430GenSourceBasis (7 : Fin 57) = [136, 70, 34, 16, 1] from rfl,
      show plane430GenSourceLb (7 : Fin 57) = 16 from rfl]
  exact plane430GenSource0007
theorem plane430GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (8 : Fin 57))) (plane430GenSourceLb (8 : Fin 57)) := by
  rw [show plane430GenSourceBasis (8 : Fin 57) = [258, 100, 16, 1] from rfl,
      show plane430GenSourceLb (8 : Fin 57) = 16 from rfl]
  exact plane430GenSource0008
theorem plane430GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis (9 : Fin 57))) (plane430GenSourceLb (9 : Fin 57)) := by
  rw [show plane430GenSourceBasis (9 : Fin 57) = [262, 100, 16, 1] from rfl,
      show plane430GenSourceLb (9 : Fin 57) = 16 from rfl]
  exact plane430GenSource0009
end QiushiMatmul
