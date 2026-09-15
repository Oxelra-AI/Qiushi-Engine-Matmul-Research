import QiushiGlobalOrbitUnused378Bindings00
import QiushiGlobalOrbitUnused378Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane378UnusedGenSourceQRA (i : Fin 17) :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenSourceBasis i)) (plane378UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane378UnusedGenBound0000
  | ⟨1, _⟩ => plane378UnusedGenBound0001
  | ⟨2, _⟩ => plane378UnusedGenBound0002
  | ⟨3, _⟩ => plane378UnusedGenBound0003
  | ⟨4, _⟩ => plane378UnusedGenBound0004
  | ⟨5, _⟩ => plane378UnusedGenBound0005
  | ⟨6, _⟩ => plane378UnusedGenBound0006
  | ⟨7, _⟩ => plane378UnusedGenBound0007
  | ⟨8, _⟩ => plane378UnusedGenBound0008
  | ⟨9, _⟩ => plane378UnusedGenBound0009
  | ⟨10, _⟩ => plane378UnusedGenBound0010
  | ⟨11, _⟩ => plane378UnusedGenBound0011
  | ⟨12, _⟩ => plane378UnusedGenBound0012
  | ⟨13, _⟩ => plane378UnusedGenBound0013
  | ⟨14, _⟩ => plane378UnusedGenBound0014
  | ⟨15, _⟩ => plane378UnusedGenBound0015
  | ⟨16, _⟩ => plane378UnusedGenBound0016
  | ⟨k + 17, h⟩ => by omega
theorem plane378UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (0 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (0 : Fin 16) = [256, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0000 (by decide)
theorem plane378UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (1 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (1 : Fin 16) = [257, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0001 (by decide)
theorem plane378UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (2 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (2 : Fin 16) = [258, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0002 (by decide)
theorem plane378UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (3 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (3 : Fin 16) = [259, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0003 (by decide)
theorem plane378UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (4 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (4 : Fin 16) = [260, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0004 (by decide)
theorem plane378UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (5 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (5 : Fin 16) = [261, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0005 (by decide)
theorem plane378UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (6 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (6 : Fin 16) = [262, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0006 (by decide)
theorem plane378UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (7 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (7 : Fin 16) = [263, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0007 (by decide)
theorem plane378UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (8 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (8 : Fin 16) = [288, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0008 (by decide)
theorem plane378UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (9 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (9 : Fin 16) = [289, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0009 (by decide)
theorem plane378UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (10 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (10 : Fin 16) = [290, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0010 (by decide)
theorem plane378UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (11 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (11 : Fin 16) = [291, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0011 (by decide)
theorem plane378UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (12 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (12 : Fin 16) = [292, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0012 (by decide)
theorem plane378UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (13 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (13 : Fin 16) = [293, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0013 (by decide)
theorem plane378UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (14 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (14 : Fin 16) = [294, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0014 (by decide)
theorem plane378UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis (15 : Fin 16))) 16 := by
  rw [show plane378UnusedGenDeadBasis (15 : Fin 16) = [295, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane378UnusedGenSource0015 (by decide)
theorem plane378UnusedGenDeadQRA (d : Fin 16) :
    QuotientRankAtLeast (spanCodes (plane378UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane378UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane378UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane378UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane378UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane378UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane378UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane378UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane378UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane378UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane378UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane378UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane378UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane378UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane378UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane378UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane378UnusedGenDeadBound0015
  | ⟨k + 16, h⟩ => by omega
end QiushiMatmul
