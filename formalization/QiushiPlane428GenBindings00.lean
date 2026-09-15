import QiushiPlane428GenSources00
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane428GenBound0000 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (0 : Fin 51))) (plane428GenSourceLb (0 : Fin 51)) := by
  rw [show plane428GenSourceBasis (0 : Fin 51) = [96, 16, 8, 1] from rfl,
      show plane428GenSourceLb (0 : Fin 51) = 16 from rfl]
  exact plane428GenSource0000
theorem plane428GenBound0001 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (1 : Fin 51))) (plane428GenSourceLb (1 : Fin 51)) := by
  rw [show plane428GenSourceBasis (1 : Fin 51) = [66, 34, 16, 1] from rfl,
      show plane428GenSourceLb (1 : Fin 51) = 16 from rfl]
  exact plane428GenSource0001
theorem plane428GenBound0002 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (2 : Fin 51))) (plane428GenSourceLb (2 : Fin 51)) := by
  rw [show plane428GenSourceBasis (2 : Fin 51) = [74, 42, 16, 1] from rfl,
      show plane428GenSourceLb (2 : Fin 51) = 16 from rfl]
  exact plane428GenSource0002
theorem plane428GenBound0003 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (3 : Fin 51))) (plane428GenSourceLb (3 : Fin 51)) := by
  rw [show plane428GenSourceBasis (3 : Fin 51) = [68, 36, 16, 14, 1] from rfl,
      show plane428GenSourceLb (3 : Fin 51) = 16 from rfl]
  exact plane428GenSource0003
theorem plane428GenBound0004 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (4 : Fin 51))) (plane428GenSourceLb (4 : Fin 51)) := by
  rw [show plane428GenSourceBasis (4 : Fin 51) = [70, 38, 16, 12, 1] from rfl,
      show plane428GenSourceLb (4 : Fin 51) = 16 from rfl]
  exact plane428GenSource0004
theorem plane428GenBound0005 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (5 : Fin 51))) (plane428GenSourceLb (5 : Fin 51)) := by
  rw [show plane428GenSourceBasis (5 : Fin 51) = [66, 34, 16, 14, 1] from rfl,
      show plane428GenSourceLb (5 : Fin 51) = 16 from rfl]
  exact plane428GenSource0005
theorem plane428GenBound0006 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (6 : Fin 51))) (plane428GenSourceLb (6 : Fin 51)) := by
  rw [show plane428GenSourceBasis (6 : Fin 51) = [66, 34, 16, 12, 1] from rfl,
      show plane428GenSourceLb (6 : Fin 51) = 16 from rfl]
  exact plane428GenSource0006
theorem plane428GenBound0007 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (7 : Fin 51))) (plane428GenSourceLb (7 : Fin 51)) := by
  rw [show plane428GenSourceBasis (7 : Fin 51) = [138, 74, 42, 16, 1] from rfl,
      show plane428GenSourceLb (7 : Fin 51) = 16 from rfl]
  exact plane428GenSource0007
theorem plane428GenBound0008 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (8 : Fin 51))) (plane428GenSourceLb (8 : Fin 51)) := by
  rw [show plane428GenSourceBasis (8 : Fin 51) = [136, 74, 42, 16, 1] from rfl,
      show plane428GenSourceLb (8 : Fin 51) = 16 from rfl]
  exact plane428GenSource0008
theorem plane428GenBound0009 :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis (9 : Fin 51))) (plane428GenSourceLb (9 : Fin 51)) := by
  rw [show plane428GenSourceBasis (9 : Fin 51) = [138, 66, 34, 16, 1] from rfl,
      show plane428GenSourceLb (9 : Fin 51) = 16 from rfl]
  exact plane428GenSource0009
end QiushiMatmul
