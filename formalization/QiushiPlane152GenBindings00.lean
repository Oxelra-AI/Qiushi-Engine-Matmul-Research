import QiushiPlane152GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane152GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (0 : Fin 16))) (plane152GenSourceLb (0 : Fin 16)) := by
  rw [show plane152GenSourceBasis (0 : Fin 16) = [164, 96, 16, 8, 2, 1] from rfl,
      show plane152GenSourceLb (0 : Fin 16) = 15 from rfl]
  exact plane152GenSource0000
theorem plane152GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (1 : Fin 16))) (plane152GenSourceLb (1 : Fin 16)) := by
  rw [show plane152GenSourceBasis (1 : Fin 16) = [256, 164, 96, 16, 10, 1] from rfl,
      show plane152GenSourceLb (1 : Fin 16) = 15 from rfl]
  exact plane152GenSource0001
theorem plane152GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (2 : Fin 16))) (plane152GenSourceLb (2 : Fin 16)) := by
  rw [show plane152GenSourceBasis (2 : Fin 16) = [262, 164, 96, 16, 10, 1] from rfl,
      show plane152GenSourceLb (2 : Fin 16) = 15 from rfl]
  exact plane152GenSource0002
theorem plane152GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (3 : Fin 16))) (plane152GenSourceLb (3 : Fin 16)) := by
  rw [show plane152GenSourceBasis (3 : Fin 16) = [290, 164, 96, 16, 10, 1] from rfl,
      show plane152GenSourceLb (3 : Fin 16) = 15 from rfl]
  exact plane152GenSource0003
theorem plane152GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (4 : Fin 16))) (plane152GenSourceLb (4 : Fin 16)) := by
  rw [show plane152GenSourceBasis (4 : Fin 16) = [294, 164, 96, 16, 10, 1] from rfl,
      show plane152GenSourceLb (4 : Fin 16) = 15 from rfl]
  exact plane152GenSource0004
theorem plane152GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (5 : Fin 16))) (plane152GenSourceLb (5 : Fin 16)) := by
  rw [show plane152GenSourceBasis (5 : Fin 16) = [256, 160, 96, 16, 10, 4, 1] from rfl,
      show plane152GenSourceLb (5 : Fin 16) = 12 from rfl]
  exact plane152GenSource0005
theorem plane152GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (6 : Fin 16))) (plane152GenSourceLb (6 : Fin 16)) := by
  rw [show plane152GenSourceBasis (6 : Fin 16) = [256, 132, 64, 32, 16, 10, 1] from rfl,
      show plane152GenSourceLb (6 : Fin 16) = 12 from rfl]
  exact plane152GenSource0006
theorem plane152GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (7 : Fin 16))) (plane152GenSourceLb (7 : Fin 16)) := by
  rw [show plane152GenSourceBasis (7 : Fin 16) = [260, 130, 70, 38, 16, 10, 1] from rfl,
      show plane152GenSourceLb (7 : Fin 16) = 12 from rfl]
  exact plane152GenSource0007
theorem plane152GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (8 : Fin 16))) (plane152GenSourceLb (8 : Fin 16)) := by
  rw [show plane152GenSourceBasis (8 : Fin 16) = [262, 134, 66, 34, 16, 10, 1] from rfl,
      show plane152GenSourceLb (8 : Fin 16) = 12 from rfl]
  exact plane152GenSource0008
theorem plane152GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis (9 : Fin 16))) (plane152GenSourceLb (9 : Fin 16)) := by
  rw [show plane152GenSourceBasis (9 : Fin 16) = [258, 128, 68, 36, 16, 10, 1] from rfl,
      show plane152GenSourceLb (9 : Fin 16) = 12 from rfl]
  exact plane152GenSource0009
end QiushiMatmul
