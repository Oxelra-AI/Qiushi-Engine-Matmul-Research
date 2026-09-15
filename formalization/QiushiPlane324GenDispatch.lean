import QiushiPlane324GenBindings00
import QiushiPlane324GenBindings01
import QiushiPlane324GenBindings02
import QiushiPlane324GenBindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane324GenSourceQRA (i : Fin 31) :
    QuotientRankAtLeast (spanCodes (plane324GenSourceBasis i)) (plane324GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane324GenBound0000
  | ⟨1, _⟩ => plane324GenBound0001
  | ⟨2, _⟩ => plane324GenBound0002
  | ⟨3, _⟩ => plane324GenBound0003
  | ⟨4, _⟩ => plane324GenBound0004
  | ⟨5, _⟩ => plane324GenBound0005
  | ⟨6, _⟩ => plane324GenBound0006
  | ⟨7, _⟩ => plane324GenBound0007
  | ⟨8, _⟩ => plane324GenBound0008
  | ⟨9, _⟩ => plane324GenBound0009
  | ⟨10, _⟩ => plane324GenBound0010
  | ⟨11, _⟩ => plane324GenBound0011
  | ⟨12, _⟩ => plane324GenBound0012
  | ⟨13, _⟩ => plane324GenBound0013
  | ⟨14, _⟩ => plane324GenBound0014
  | ⟨15, _⟩ => plane324GenBound0015
  | ⟨16, _⟩ => plane324GenBound0016
  | ⟨17, _⟩ => plane324GenBound0017
  | ⟨18, _⟩ => plane324GenBound0018
  | ⟨19, _⟩ => plane324GenBound0019
  | ⟨20, _⟩ => plane324GenBound0020
  | ⟨21, _⟩ => plane324GenBound0021
  | ⟨22, _⟩ => plane324GenBound0022
  | ⟨23, _⟩ => plane324GenBound0023
  | ⟨24, _⟩ => plane324GenBound0024
  | ⟨25, _⟩ => plane324GenBound0025
  | ⟨26, _⟩ => plane324GenBound0026
  | ⟨27, _⟩ => plane324GenBound0027
  | ⟨28, _⟩ => plane324GenBound0028
  | ⟨29, _⟩ => plane324GenBound0029
  | ⟨30, _⟩ => plane324GenBound0030
  | ⟨k + 31, h⟩ => by omega
theorem plane324GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (0 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (0 : Fin 17) = [196, 36, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0000 (by decide)
theorem plane324GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (1 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (1 : Fin 17) = [196, 36, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0001 (by decide)
theorem plane324GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (2 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (2 : Fin 17) = [196, 36, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0002 (by decide)
theorem plane324GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (3 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (3 : Fin 17) = [134, 66, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0003 (by decide)
theorem plane324GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (4 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (4 : Fin 17) = [142, 74, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0004 (by decide)
theorem plane324GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (5 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (5 : Fin 17) = [136, 76, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0005 (by decide)
theorem plane324GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (6 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (6 : Fin 17) = [138, 78, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0006 (by decide)
theorem plane324GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (7 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (7 : Fin 17) = [258, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0007 (by decide)
theorem plane324GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (8 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (8 : Fin 17) = [262, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0008 (by decide)
theorem plane324GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (9 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (9 : Fin 17) = [264, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0009 (by decide)
theorem plane324GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (10 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (10 : Fin 17) = [266, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0010 (by decide)
theorem plane324GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (11 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (11 : Fin 17) = [268, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0011 (by decide)
theorem plane324GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (12 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (12 : Fin 17) = [270, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0012 (by decide)
theorem plane324GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (13 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (13 : Fin 17) = [326, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0013 (by decide)
theorem plane324GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (14 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (14 : Fin 17) = [328, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0014 (by decide)
theorem plane324GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (15 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (15 : Fin 17) = [330, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0015 (by decide)
theorem plane324GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis (16 : Fin 17))) 15 := by
  rw [show plane324GenDeadBasis (16 : Fin 17) = [334, 196, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane324GenSource0016 (by decide)
theorem plane324GenDeadQRA (d : Fin 17) :
    QuotientRankAtLeast (spanCodes (plane324GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane324GenDeadBound0000
  | ⟨1, _⟩ => plane324GenDeadBound0001
  | ⟨2, _⟩ => plane324GenDeadBound0002
  | ⟨3, _⟩ => plane324GenDeadBound0003
  | ⟨4, _⟩ => plane324GenDeadBound0004
  | ⟨5, _⟩ => plane324GenDeadBound0005
  | ⟨6, _⟩ => plane324GenDeadBound0006
  | ⟨7, _⟩ => plane324GenDeadBound0007
  | ⟨8, _⟩ => plane324GenDeadBound0008
  | ⟨9, _⟩ => plane324GenDeadBound0009
  | ⟨10, _⟩ => plane324GenDeadBound0010
  | ⟨11, _⟩ => plane324GenDeadBound0011
  | ⟨12, _⟩ => plane324GenDeadBound0012
  | ⟨13, _⟩ => plane324GenDeadBound0013
  | ⟨14, _⟩ => plane324GenDeadBound0014
  | ⟨15, _⟩ => plane324GenDeadBound0015
  | ⟨16, _⟩ => plane324GenDeadBound0016
  | ⟨k + 17, h⟩ => by omega
end QiushiMatmul
