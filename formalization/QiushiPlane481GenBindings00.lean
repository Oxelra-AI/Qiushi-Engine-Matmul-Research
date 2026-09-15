import QiushiPlane481GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane481GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (0 : Fin 116))) (plane481GenSourceLb (0 : Fin 116)) := by
  rw [show plane481GenSourceBasis (0 : Fin 116) = [20, 2, 1] from rfl,
      show plane481GenSourceLb (0 : Fin 116) = 17 from rfl]
  exact plane481GenSource0000
theorem plane481GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (1 : Fin 116))) (plane481GenSourceLb (1 : Fin 116)) := by
  rw [show plane481GenSourceBasis (1 : Fin 116) = [20, 8, 1] from rfl,
      show plane481GenSourceLb (1 : Fin 116) = 17 from rfl]
  exact plane481GenSource0001
theorem plane481GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (2 : Fin 116))) (plane481GenSourceLb (2 : Fin 116)) := by
  rw [show plane481GenSourceBasis (2 : Fin 116) = [38, 20, 1] from rfl,
      show plane481GenSourceLb (2 : Fin 116) = 17 from rfl]
  exact plane481GenSource0002
theorem plane481GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (3 : Fin 116))) (plane481GenSourceLb (3 : Fin 116)) := by
  rw [show plane481GenSourceBasis (3 : Fin 116) = [46, 20, 1] from rfl,
      show plane481GenSourceLb (3 : Fin 116) = 17 from rfl]
  exact plane481GenSource0003
theorem plane481GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (4 : Fin 116))) (plane481GenSourceLb (4 : Fin 116)) := by
  rw [show plane481GenSourceBasis (4 : Fin 116) = [64, 20, 1] from rfl,
      show plane481GenSourceLb (4 : Fin 116) = 17 from rfl]
  exact plane481GenSource0004
theorem plane481GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (5 : Fin 116))) (plane481GenSourceLb (5 : Fin 116)) := by
  rw [show plane481GenSourceBasis (5 : Fin 116) = [68, 20, 2, 1] from rfl,
      show plane481GenSourceLb (5 : Fin 116) = 17 from rfl]
  exact plane481GenSource0005
theorem plane481GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (6 : Fin 116))) (plane481GenSourceLb (6 : Fin 116)) := by
  rw [show plane481GenSourceBasis (6 : Fin 116) = [72, 20, 1] from rfl,
      show plane481GenSourceLb (6 : Fin 116) = 17 from rfl]
  exact plane481GenSource0006
theorem plane481GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (7 : Fin 116))) (plane481GenSourceLb (7 : Fin 116)) := by
  rw [show plane481GenSourceBasis (7 : Fin 116) = [68, 20, 14, 1] from rfl,
      show plane481GenSourceLb (7 : Fin 116) = 17 from rfl]
  exact plane481GenSource0007
theorem plane481GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (8 : Fin 116))) (plane481GenSourceLb (8 : Fin 116)) := by
  rw [show plane481GenSourceBasis (8 : Fin 116) = [70, 20, 12, 1] from rfl,
      show plane481GenSourceLb (8 : Fin 116) = 17 from rfl]
  exact plane481GenSource0008
theorem plane481GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis (9 : Fin 116))) (plane481GenSourceLb (9 : Fin 116)) := by
  rw [show plane481GenSourceBasis (9 : Fin 116) = [66, 20, 14, 1] from rfl,
      show plane481GenSourceLb (9 : Fin 116) = 17 from rfl]
  exact plane481GenSource0009
end QiushiMatmul
