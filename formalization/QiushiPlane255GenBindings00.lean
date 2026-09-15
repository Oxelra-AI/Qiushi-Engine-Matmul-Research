import QiushiPlane255GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane255GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (0 : Fin 25))) (plane255GenSourceLb (0 : Fin 25)) := by
  rw [show plane255GenSourceBasis (0 : Fin 25) = [96, 16, 8, 2, 1] from rfl,
      show plane255GenSourceLb (0 : Fin 25) = 15 from rfl]
  exact plane255GenSource0000
theorem plane255GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (1 : Fin 25))) (plane255GenSourceLb (1 : Fin 25)) := by
  rw [show plane255GenSourceBasis (1 : Fin 25) = [96, 20, 8, 2, 1] from rfl,
      show plane255GenSourceLb (1 : Fin 25) = 15 from rfl]
  exact plane255GenSource0001
theorem plane255GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (2 : Fin 25))) (plane255GenSourceLb (2 : Fin 25)) := by
  rw [show plane255GenSourceBasis (2 : Fin 25) = [68, 36, 8, 2, 1] from rfl,
      show plane255GenSourceLb (2 : Fin 25) = 15 from rfl]
  exact plane255GenSource0002
theorem plane255GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (3 : Fin 25))) (plane255GenSourceLb (3 : Fin 25)) := by
  rw [show plane255GenSourceBasis (3 : Fin 25) = [80, 48, 8, 2, 1] from rfl,
      show plane255GenSourceLb (3 : Fin 25) = 15 from rfl]
  exact plane255GenSource0003
theorem plane255GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (4 : Fin 25))) (plane255GenSourceLb (4 : Fin 25)) := by
  rw [show plane255GenSourceBasis (4 : Fin 25) = [84, 52, 8, 2, 1] from rfl,
      show plane255GenSourceLb (4 : Fin 25) = 15 from rfl]
  exact plane255GenSource0004
theorem plane255GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (5 : Fin 25))) (plane255GenSourceLb (5 : Fin 25)) := by
  rw [show plane255GenSourceBasis (5 : Fin 25) = [128, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (5 : Fin 25) = 15 from rfl]
  exact plane255GenSource0005
theorem plane255GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (6 : Fin 25))) (plane255GenSourceLb (6 : Fin 25)) := by
  rw [show plane255GenSourceBasis (6 : Fin 25) = [132, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (6 : Fin 25) = 15 from rfl]
  exact plane255GenSource0006
theorem plane255GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (7 : Fin 25))) (plane255GenSourceLb (7 : Fin 25)) := by
  rw [show plane255GenSourceBasis (7 : Fin 25) = [144, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (7 : Fin 25) = 15 from rfl]
  exact plane255GenSource0007
theorem plane255GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (8 : Fin 25))) (plane255GenSourceLb (8 : Fin 25)) := by
  rw [show plane255GenSourceBasis (8 : Fin 25) = [148, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (8 : Fin 25) = 15 from rfl]
  exact plane255GenSource0008
theorem plane255GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis (9 : Fin 25))) (plane255GenSourceLb (9 : Fin 25)) := by
  rw [show plane255GenSourceBasis (9 : Fin 25) = [160, 96, 8, 2, 1] from rfl,
      show plane255GenSourceLb (9 : Fin 25) = 15 from rfl]
  exact plane255GenSource0009
end QiushiMatmul
