import QiushiPlane433GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (0 : Fin 63))) (plane433GenSourceLb (0 : Fin 63)) := by
  rw [show plane433GenSourceBasis (0 : Fin 63) = [258, 16, 10, 1] from rfl,
      show plane433GenSourceLb (0 : Fin 63) = 17 from rfl]
  exact plane433GenSource0000
theorem plane433GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (1 : Fin 63))) (plane433GenSourceLb (1 : Fin 63)) := by
  rw [show plane433GenSourceBasis (1 : Fin 63) = [258, 16, 4, 1] from rfl,
      show plane433GenSourceLb (1 : Fin 63) = 16 from rfl]
  exact plane433GenSource0001
theorem plane433GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (2 : Fin 63))) (plane433GenSourceLb (2 : Fin 63)) := by
  rw [show plane433GenSourceBasis (2 : Fin 63) = [258, 16, 12, 1] from rfl,
      show plane433GenSourceLb (2 : Fin 63) = 16 from rfl]
  exact plane433GenSource0002
theorem plane433GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (3 : Fin 63))) (plane433GenSourceLb (3 : Fin 63)) := by
  rw [show plane433GenSourceBasis (3 : Fin 63) = [258, 16, 14, 1] from rfl,
      show plane433GenSourceLb (3 : Fin 63) = 16 from rfl]
  exact plane433GenSource0003
theorem plane433GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (4 : Fin 63))) (plane433GenSourceLb (4 : Fin 63)) := by
  rw [show plane433GenSourceBasis (4 : Fin 63) = [258, 42, 16, 1] from rfl,
      show plane433GenSourceLb (4 : Fin 63) = 16 from rfl]
  exact plane433GenSource0004
theorem plane433GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (5 : Fin 63))) (plane433GenSourceLb (5 : Fin 63)) := by
  rw [show plane433GenSourceBasis (5 : Fin 63) = [258, 36, 16, 14, 1] from rfl,
      show plane433GenSourceLb (5 : Fin 63) = 16 from rfl]
  exact plane433GenSource0005
theorem plane433GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (6 : Fin 63))) (plane433GenSourceLb (6 : Fin 63)) := by
  rw [show plane433GenSourceBasis (6 : Fin 63) = [258, 68, 16, 1] from rfl,
      show plane433GenSourceLb (6 : Fin 63) = 16 from rfl]
  exact plane433GenSource0006
theorem plane433GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (7 : Fin 63))) (plane433GenSourceLb (7 : Fin 63)) := by
  rw [show plane433GenSourceBasis (7 : Fin 63) = [258, 74, 16, 1] from rfl,
      show plane433GenSourceLb (7 : Fin 63) = 16 from rfl]
  exact plane433GenSource0007
theorem plane433GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (8 : Fin 63))) (plane433GenSourceLb (8 : Fin 63)) := by
  rw [show plane433GenSourceBasis (8 : Fin 63) = [258, 76, 16, 1] from rfl,
      show plane433GenSourceLb (8 : Fin 63) = 16 from rfl]
  exact plane433GenSource0008
theorem plane433GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis (9 : Fin 63))) (plane433GenSourceLb (9 : Fin 63)) := by
  rw [show plane433GenSourceBasis (9 : Fin 63) = [258, 78, 16, 1] from rfl,
      show plane433GenSourceLb (9 : Fin 63) = 16 from rfl]
  exact plane433GenSource0009
end QiushiMatmul
