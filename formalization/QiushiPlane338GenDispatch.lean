import QiushiPlane338GenBindings00
import QiushiPlane338GenBindings01
import QiushiPlane338GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane338GenSourceQRA (i : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane338GenSourceBasis i)) (plane338GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane338GenBound0000
  | ⟨1, _⟩ => plane338GenBound0001
  | ⟨2, _⟩ => plane338GenBound0002
  | ⟨3, _⟩ => plane338GenBound0003
  | ⟨4, _⟩ => plane338GenBound0004
  | ⟨5, _⟩ => plane338GenBound0005
  | ⟨6, _⟩ => plane338GenBound0006
  | ⟨7, _⟩ => plane338GenBound0007
  | ⟨8, _⟩ => plane338GenBound0008
  | ⟨9, _⟩ => plane338GenBound0009
  | ⟨10, _⟩ => plane338GenBound0010
  | ⟨11, _⟩ => plane338GenBound0011
  | ⟨12, _⟩ => plane338GenBound0012
  | ⟨13, _⟩ => plane338GenBound0013
  | ⟨14, _⟩ => plane338GenBound0014
  | ⟨15, _⟩ => plane338GenBound0015
  | ⟨16, _⟩ => plane338GenBound0016
  | ⟨17, _⟩ => plane338GenBound0017
  | ⟨18, _⟩ => plane338GenBound0018
  | ⟨19, _⟩ => plane338GenBound0019
  | ⟨20, _⟩ => plane338GenBound0020
  | ⟨k + 21, h⟩ => by omega
theorem plane338GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (0 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (0 : Fin 15) = [288, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0000 (by decide)
theorem plane338GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (1 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (1 : Fin 15) = [288, 98, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0001 (by decide)
theorem plane338GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (2 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (2 : Fin 15) = [288, 98, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0002 (by decide)
theorem plane338GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (3 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (3 : Fin 15) = [268, 78, 44, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0003 (by decide)
theorem plane338GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (4 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (4 : Fin 15) = [288, 132, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0004 (by decide)
theorem plane338GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (5 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (5 : Fin 15) = [288, 134, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0005 (by decide)
theorem plane338GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (6 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (6 : Fin 15) = [288, 136, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0006 (by decide)
theorem plane338GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (7 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (7 : Fin 15) = [288, 138, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0007 (by decide)
theorem plane338GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (8 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (8 : Fin 15) = [288, 140, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0008 (by decide)
theorem plane338GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (9 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (9 : Fin 15) = [288, 142, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0009 (by decide)
theorem plane338GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (10 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (10 : Fin 15) = [288, 162, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0010 (by decide)
theorem plane338GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (11 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (11 : Fin 15) = [288, 164, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0011 (by decide)
theorem plane338GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (12 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (12 : Fin 15) = [288, 166, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0012 (by decide)
theorem plane338GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (13 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (13 : Fin 15) = [288, 172, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0013 (by decide)
theorem plane338GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis (14 : Fin 15))) 15 := by
  rw [show plane338GenDeadBasis (14 : Fin 15) = [288, 174, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane338GenSource0014 (by decide)
theorem plane338GenDeadQRA (d : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane338GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane338GenDeadBound0000
  | ⟨1, _⟩ => plane338GenDeadBound0001
  | ⟨2, _⟩ => plane338GenDeadBound0002
  | ⟨3, _⟩ => plane338GenDeadBound0003
  | ⟨4, _⟩ => plane338GenDeadBound0004
  | ⟨5, _⟩ => plane338GenDeadBound0005
  | ⟨6, _⟩ => plane338GenDeadBound0006
  | ⟨7, _⟩ => plane338GenDeadBound0007
  | ⟨8, _⟩ => plane338GenDeadBound0008
  | ⟨9, _⟩ => plane338GenDeadBound0009
  | ⟨10, _⟩ => plane338GenDeadBound0010
  | ⟨11, _⟩ => plane338GenDeadBound0011
  | ⟨12, _⟩ => plane338GenDeadBound0012
  | ⟨13, _⟩ => plane338GenDeadBound0013
  | ⟨14, _⟩ => plane338GenDeadBound0014
  | ⟨k + 15, h⟩ => by omega
end QiushiMatmul
