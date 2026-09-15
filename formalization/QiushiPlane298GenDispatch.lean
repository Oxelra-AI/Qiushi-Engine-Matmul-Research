import QiushiPlane298GenBindings00
import QiushiPlane298GenBindings01
import QiushiPlane298GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane298GenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane298GenSourceBasis i)) (plane298GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane298GenBound0000
  | ⟨1, _⟩ => plane298GenBound0001
  | ⟨2, _⟩ => plane298GenBound0002
  | ⟨3, _⟩ => plane298GenBound0003
  | ⟨4, _⟩ => plane298GenBound0004
  | ⟨5, _⟩ => plane298GenBound0005
  | ⟨6, _⟩ => plane298GenBound0006
  | ⟨7, _⟩ => plane298GenBound0007
  | ⟨8, _⟩ => plane298GenBound0008
  | ⟨9, _⟩ => plane298GenBound0009
  | ⟨10, _⟩ => plane298GenBound0010
  | ⟨11, _⟩ => plane298GenBound0011
  | ⟨12, _⟩ => plane298GenBound0012
  | ⟨13, _⟩ => plane298GenBound0013
  | ⟨14, _⟩ => plane298GenBound0014
  | ⟨15, _⟩ => plane298GenBound0015
  | ⟨16, _⟩ => plane298GenBound0016
  | ⟨17, _⟩ => plane298GenBound0017
  | ⟨18, _⟩ => plane298GenBound0018
  | ⟨19, _⟩ => plane298GenBound0019
  | ⟨20, _⟩ => plane298GenBound0020
  | ⟨21, _⟩ => plane298GenBound0021
  | ⟨22, _⟩ => plane298GenBound0022
  | ⟨23, _⟩ => plane298GenBound0023
  | ⟨24, _⟩ => plane298GenBound0024
  | ⟨25, _⟩ => plane298GenBound0025
  | ⟨26, _⟩ => plane298GenBound0026
  | ⟨27, _⟩ => plane298GenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane298GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (0 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (0 : Fin 18) = [384, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0000 (by decide)
theorem plane298GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (1 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (1 : Fin 18) = [384, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0001 (by decide)
theorem plane298GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (2 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (2 : Fin 18) = [384, 70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0002 (by decide)
theorem plane298GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (3 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (3 : Fin 18) = [384, 80, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0003 (by decide)
theorem plane298GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (4 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (4 : Fin 18) = [384, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0004 (by decide)
theorem plane298GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (5 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (5 : Fin 18) = [384, 86, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0005 (by decide)
theorem plane298GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (6 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (6 : Fin 18) = [258, 130, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0006 (by decide)
theorem plane298GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (7 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (7 : Fin 18) = [262, 134, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0007 (by decide)
theorem plane298GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (8 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (8 : Fin 18) = [272, 144, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0008 (by decide)
theorem plane298GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (9 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (9 : Fin 18) = [274, 146, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0009 (by decide)
theorem plane298GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (10 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (10 : Fin 18) = [276, 148, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0010 (by decide)
theorem plane298GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (11 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (11 : Fin 18) = [278, 150, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0011 (by decide)
theorem plane298GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (12 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (12 : Fin 18) = [324, 196, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0012 (by decide)
theorem plane298GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (13 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (13 : Fin 18) = [326, 198, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0013 (by decide)
theorem plane298GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (14 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (14 : Fin 18) = [336, 208, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0014 (by decide)
theorem plane298GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (15 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (15 : Fin 18) = [338, 210, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0015 (by decide)
theorem plane298GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (16 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (16 : Fin 18) = [340, 212, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0016 (by decide)
theorem plane298GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis (17 : Fin 18))) 15 := by
  rw [show plane298GenDeadBasis (17 : Fin 18) = [342, 214, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane298GenSource0017 (by decide)
theorem plane298GenDeadQRA (d : Fin 18) :
    QuotientRankAtLeast (spanCodes (plane298GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane298GenDeadBound0000
  | ⟨1, _⟩ => plane298GenDeadBound0001
  | ⟨2, _⟩ => plane298GenDeadBound0002
  | ⟨3, _⟩ => plane298GenDeadBound0003
  | ⟨4, _⟩ => plane298GenDeadBound0004
  | ⟨5, _⟩ => plane298GenDeadBound0005
  | ⟨6, _⟩ => plane298GenDeadBound0006
  | ⟨7, _⟩ => plane298GenDeadBound0007
  | ⟨8, _⟩ => plane298GenDeadBound0008
  | ⟨9, _⟩ => plane298GenDeadBound0009
  | ⟨10, _⟩ => plane298GenDeadBound0010
  | ⟨11, _⟩ => plane298GenDeadBound0011
  | ⟨12, _⟩ => plane298GenDeadBound0012
  | ⟨13, _⟩ => plane298GenDeadBound0013
  | ⟨14, _⟩ => plane298GenDeadBound0014
  | ⟨15, _⟩ => plane298GenDeadBound0015
  | ⟨16, _⟩ => plane298GenDeadBound0016
  | ⟨17, _⟩ => plane298GenDeadBound0017
  | ⟨k + 18, h⟩ => by omega
end QiushiMatmul
