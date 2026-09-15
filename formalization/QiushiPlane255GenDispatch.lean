import QiushiPlane255GenBindings00
import QiushiPlane255GenBindings01
import QiushiPlane255GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane255GenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane255GenSourceBasis i)) (plane255GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane255GenBound0000
  | ⟨1, _⟩ => plane255GenBound0001
  | ⟨2, _⟩ => plane255GenBound0002
  | ⟨3, _⟩ => plane255GenBound0003
  | ⟨4, _⟩ => plane255GenBound0004
  | ⟨5, _⟩ => plane255GenBound0005
  | ⟨6, _⟩ => plane255GenBound0006
  | ⟨7, _⟩ => plane255GenBound0007
  | ⟨8, _⟩ => plane255GenBound0008
  | ⟨9, _⟩ => plane255GenBound0009
  | ⟨10, _⟩ => plane255GenBound0010
  | ⟨11, _⟩ => plane255GenBound0011
  | ⟨12, _⟩ => plane255GenBound0012
  | ⟨13, _⟩ => plane255GenBound0013
  | ⟨14, _⟩ => plane255GenBound0014
  | ⟨15, _⟩ => plane255GenBound0015
  | ⟨16, _⟩ => plane255GenBound0016
  | ⟨17, _⟩ => plane255GenBound0017
  | ⟨18, _⟩ => plane255GenBound0018
  | ⟨19, _⟩ => plane255GenBound0019
  | ⟨20, _⟩ => plane255GenBound0020
  | ⟨21, _⟩ => plane255GenBound0021
  | ⟨22, _⟩ => plane255GenBound0022
  | ⟨23, _⟩ => plane255GenBound0023
  | ⟨24, _⟩ => plane255GenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane255GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (0 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (0 : Fin 17) = [96, 16, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0000 (by decide)
theorem plane255GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (1 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (1 : Fin 17) = [96, 20, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0001 (by decide)
theorem plane255GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (2 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (2 : Fin 17) = [68, 36, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0002 (by decide)
theorem plane255GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (3 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (3 : Fin 17) = [80, 48, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0003 (by decide)
theorem plane255GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (4 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (4 : Fin 17) = [84, 52, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0004 (by decide)
theorem plane255GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (5 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (5 : Fin 17) = [128, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0005 (by decide)
theorem plane255GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (6 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (6 : Fin 17) = [132, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0006 (by decide)
theorem plane255GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (7 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (7 : Fin 17) = [144, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0007 (by decide)
theorem plane255GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (8 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (8 : Fin 17) = [148, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0008 (by decide)
theorem plane255GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (9 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (9 : Fin 17) = [160, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0009 (by decide)
theorem plane255GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (10 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (10 : Fin 17) = [164, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0010 (by decide)
theorem plane255GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (11 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (11 : Fin 17) = [176, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0011 (by decide)
theorem plane255GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (12 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (12 : Fin 17) = [180, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0012 (by decide)
theorem plane255GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (13 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (13 : Fin 17) = [272, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0013 (by decide)
theorem plane255GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (14 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (14 : Fin 17) = [276, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0014 (by decide)
theorem plane255GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (15 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (15 : Fin 17) = [304, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0015 (by decide)
theorem plane255GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis (16 : Fin 17))) 15 := by
  rw [show plane255GenDeadBasis (16 : Fin 17) = [308, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane255GenSource0016 (by decide)
theorem plane255GenDeadQRA (d : Fin 17) :
    QuotientRankAtLeast (spanCodes (plane255GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane255GenDeadBound0000
  | ⟨1, _⟩ => plane255GenDeadBound0001
  | ⟨2, _⟩ => plane255GenDeadBound0002
  | ⟨3, _⟩ => plane255GenDeadBound0003
  | ⟨4, _⟩ => plane255GenDeadBound0004
  | ⟨5, _⟩ => plane255GenDeadBound0005
  | ⟨6, _⟩ => plane255GenDeadBound0006
  | ⟨7, _⟩ => plane255GenDeadBound0007
  | ⟨8, _⟩ => plane255GenDeadBound0008
  | ⟨9, _⟩ => plane255GenDeadBound0009
  | ⟨10, _⟩ => plane255GenDeadBound0010
  | ⟨11, _⟩ => plane255GenDeadBound0011
  | ⟨12, _⟩ => plane255GenDeadBound0012
  | ⟨13, _⟩ => plane255GenDeadBound0013
  | ⟨14, _⟩ => plane255GenDeadBound0014
  | ⟨15, _⟩ => plane255GenDeadBound0015
  | ⟨16, _⟩ => plane255GenDeadBound0016
  | ⟨k + 17, h⟩ => by omega
end QiushiMatmul
