import QiushiPlane448GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane448GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (0 : Fin 56))) (plane448GenSourceLb (0 : Fin 56)) := by
  rw [show plane448GenSourceBasis (0 : Fin 56) = [304, 160, 10, 1] from rfl,
      show plane448GenSourceLb (0 : Fin 56) = 16 from rfl]
  exact plane448GenSource0000
theorem plane448GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (1 : Fin 56))) (plane448GenSourceLb (1 : Fin 56)) := by
  rw [show plane448GenSourceBasis (1 : Fin 56) = [280, 130, 34, 1] from rfl,
      show plane448GenSourceLb (1 : Fin 56) = 16 from rfl]
  exact plane448GenSource0001
theorem plane448GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (2 : Fin 56))) (plane448GenSourceLb (2 : Fin 56)) := by
  rw [show plane448GenSourceBasis (2 : Fin 56) = [286, 132, 36, 1] from rfl,
      show plane448GenSourceLb (2 : Fin 56) = 16 from rfl]
  exact plane448GenSource0002
theorem plane448GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (3 : Fin 56))) (plane448GenSourceLb (3 : Fin 56)) := by
  rw [show plane448GenSourceBasis (3 : Fin 56) = [284, 134, 38, 1] from rfl,
      show plane448GenSourceLb (3 : Fin 56) = 16 from rfl]
  exact plane448GenSource0003
theorem plane448GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (4 : Fin 56))) (plane448GenSourceLb (4 : Fin 56)) := by
  rw [show plane448GenSourceBasis (4 : Fin 56) = [274, 136, 40, 1] from rfl,
      show plane448GenSourceLb (4 : Fin 56) = 16 from rfl]
  exact plane448GenSource0004
theorem plane448GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (5 : Fin 56))) (plane448GenSourceLb (5 : Fin 56)) := by
  rw [show plane448GenSourceBasis (5 : Fin 56) = [274, 132, 36, 12, 1] from rfl,
      show plane448GenSourceLb (5 : Fin 56) = 16 from rfl]
  exact plane448GenSource0005
theorem plane448GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (6 : Fin 56))) (plane448GenSourceLb (6 : Fin 56)) := by
  rw [show plane448GenSourceBasis (6 : Fin 56) = [272, 138, 42, 1] from rfl,
      show plane448GenSourceLb (6 : Fin 56) = 16 from rfl]
  exact plane448GenSource0006
theorem plane448GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (7 : Fin 56))) (plane448GenSourceLb (7 : Fin 56)) := by
  rw [show plane448GenSourceBasis (7 : Fin 56) = [276, 142, 46, 1] from rfl,
      show plane448GenSourceLb (7 : Fin 56) = 16 from rfl]
  exact plane448GenSource0007
theorem plane448GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (8 : Fin 56))) (plane448GenSourceLb (8 : Fin 56)) := by
  rw [show plane448GenSourceBasis (8 : Fin 56) = [264, 146, 50, 1] from rfl,
      show plane448GenSourceLb (8 : Fin 56) = 16 from rfl]
  exact plane448GenSource0008
theorem plane448GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis (9 : Fin 56))) (plane448GenSourceLb (9 : Fin 56)) := by
  rw [show plane448GenSourceBasis (9 : Fin 56) = [270, 148, 52, 1] from rfl,
      show plane448GenSourceLb (9 : Fin 56) = 16 from rfl]
  exact plane448GenSource0009
end QiushiMatmul
