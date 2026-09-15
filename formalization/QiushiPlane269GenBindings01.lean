import QiushiPlane269GenSources01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane269GenBound0010 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (10 : Fin 30))) (plane269GenSourceLb (10 : Fin 30)) := by
  rw [show plane269GenSourceBasis (10 : Fin 30) = [264, 144, 32, 2, 1] from rfl,
      show plane269GenSourceLb (10 : Fin 30) = 14 from rfl]
  exact plane269GenSource0010
theorem plane269GenBound0011 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (11 : Fin 30))) (plane269GenSourceLb (11 : Fin 30)) := by
  rw [show plane269GenSourceBasis (11 : Fin 30) = [264, 192, 32, 2, 1] from rfl,
      show plane269GenSourceLb (11 : Fin 30) = 14 from rfl]
  exact plane269GenSource0011
theorem plane269GenBound0012 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (12 : Fin 30))) (plane269GenSourceLb (12 : Fin 30)) := by
  rw [show plane269GenSourceBasis (12 : Fin 30) = [264, 64, 32, 4, 2, 1] from rfl,
      show plane269GenSourceLb (12 : Fin 30) = 12 from rfl]
  exact plane269GenSource0012
theorem plane269GenBound0013 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (13 : Fin 30))) (plane269GenSourceLb (13 : Fin 30)) := by
  rw [show plane269GenSourceBasis (13 : Fin 30) = [264, 72, 32, 4, 2, 1] from rfl,
      show plane269GenSourceLb (13 : Fin 30) = 12 from rfl]
  exact plane269GenSource0013
theorem plane269GenBound0014 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (14 : Fin 30))) (plane269GenSourceLb (14 : Fin 30)) := by
  rw [show plane269GenSourceBasis (14 : Fin 30) = [260, 132, 64, 32, 12, 2, 1] from rfl,
      show plane269GenSourceLb (14 : Fin 30) = 12 from rfl]
  exact plane269GenSource0014
theorem plane269GenBound0015 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (15 : Fin 30))) (plane269GenSourceLb (15 : Fin 30)) := by
  rw [show plane269GenSourceBasis (15 : Fin 30) = [260, 148, 84, 32, 12, 2, 1] from rfl,
      show plane269GenSourceLb (15 : Fin 30) = 12 from rfl]
  exact plane269GenSource0015
theorem plane269GenBound0016 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (16 : Fin 30))) (plane269GenSourceLb (16 : Fin 30)) := by
  rw [show plane269GenSourceBasis (16 : Fin 30) = [256, 148, 80, 32, 8, 2, 1] from rfl,
      show plane269GenSourceLb (16 : Fin 30) = 12 from rfl]
  exact plane269GenSource0016
theorem plane269GenBound0017 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (17 : Fin 30))) (plane269GenSourceLb (17 : Fin 30)) := by
  rw [show plane269GenSourceBasis (17 : Fin 30) = [264, 128, 76, 32, 28, 2, 1] from rfl,
      show plane269GenSourceLb (17 : Fin 30) = 12 from rfl]
  exact plane269GenSource0017
theorem plane269GenBound0018 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (18 : Fin 30))) (plane269GenSourceLb (18 : Fin 30)) := by
  rw [show plane269GenSourceBasis (18 : Fin 30) = [264, 140, 68, 32, 28, 2, 1] from rfl,
      show plane269GenSourceLb (18 : Fin 30) = 12 from rfl]
  exact plane269GenSource0018
theorem plane269GenBound0019 :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis (19 : Fin 30))) (plane269GenSourceLb (19 : Fin 30)) := by
  rw [show plane269GenSourceBasis (19 : Fin 30) = [264, 136, 64, 32, 28, 2, 1] from rfl,
      show plane269GenSourceLb (19 : Fin 30) = 12 from rfl]
  exact plane269GenSource0019
end QiushiMatmul
