import QiushiPlane429GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane429GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (0 : Fin 55))) (plane429GenSourceLb (0 : Fin 55)) := by
  rw [show plane429GenSourceBasis (0 : Fin 55) = [140, 98, 16, 1] from rfl,
      show plane429GenSourceLb (0 : Fin 55) = 16 from rfl]
  exact plane429GenSource0000
theorem plane429GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (1 : Fin 55))) (plane429GenSourceLb (1 : Fin 55)) := by
  rw [show plane429GenSourceBasis (1 : Fin 55) = [142, 98, 16, 1] from rfl,
      show plane429GenSourceLb (1 : Fin 55) = 16 from rfl]
  exact plane429GenSource0001
theorem plane429GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (2 : Fin 55))) (plane429GenSourceLb (2 : Fin 55)) := by
  rw [show plane429GenSourceBasis (2 : Fin 55) = [96, 16, 8, 2, 1] from rfl,
      show plane429GenSourceLb (2 : Fin 55) = 15 from rfl]
  exact plane429GenSource0002
theorem plane429GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (3 : Fin 55))) (plane429GenSourceLb (3 : Fin 55)) := by
  rw [show plane429GenSourceBasis (3 : Fin 55) = [70, 36, 16, 8, 1] from rfl,
      show plane429GenSourceLb (3 : Fin 55) = 15 from rfl]
  exact plane429GenSource0003
theorem plane429GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (4 : Fin 55))) (plane429GenSourceLb (4 : Fin 55)) := by
  rw [show plane429GenSourceBasis (4 : Fin 55) = [130, 98, 16, 8, 1] from rfl,
      show plane429GenSourceLb (4 : Fin 55) = 15 from rfl]
  exact plane429GenSource0004
theorem plane429GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (5 : Fin 55))) (plane429GenSourceLb (5 : Fin 55)) := by
  rw [show plane429GenSourceBasis (5 : Fin 55) = [128, 64, 34, 16, 1] from rfl,
      show plane429GenSourceLb (5 : Fin 55) = 15 from rfl]
  exact plane429GenSource0005
theorem plane429GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (6 : Fin 55))) (plane429GenSourceLb (6 : Fin 55)) := by
  rw [show plane429GenSourceBasis (6 : Fin 55) = [136, 76, 44, 16, 2, 1] from rfl,
      show plane429GenSourceLb (6 : Fin 55) = 15 from rfl]
  exact plane429GenSource0006
theorem plane429GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (7 : Fin 55))) (plane429GenSourceLb (7 : Fin 55)) := by
  rw [show plane429GenSourceBasis (7 : Fin 55) = [160, 98, 16, 8, 1] from rfl,
      show plane429GenSourceLb (7 : Fin 55) = 15 from rfl]
  exact plane429GenSource0007
theorem plane429GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (8 : Fin 55))) (plane429GenSourceLb (8 : Fin 55)) := by
  rw [show plane429GenSourceBasis (8 : Fin 55) = [162, 98, 16, 8, 1] from rfl,
      show plane429GenSourceLb (8 : Fin 55) = 15 from rfl]
  exact plane429GenSource0008
theorem plane429GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis (9 : Fin 55))) (plane429GenSourceLb (9 : Fin 55)) := by
  rw [show plane429GenSourceBasis (9 : Fin 55) = [164, 96, 16, 12, 2, 1] from rfl,
      show plane429GenSourceLb (9 : Fin 55) = 15 from rfl]
  exact plane429GenSource0009
end QiushiMatmul
