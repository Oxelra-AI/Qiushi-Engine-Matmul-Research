import QiushiPlane292GenBindings00
import QiushiPlane292GenBindings01
import QiushiPlane292GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane292GenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane292GenSourceBasis i)) (plane292GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane292GenBound0000
  | ⟨1, _⟩ => plane292GenBound0001
  | ⟨2, _⟩ => plane292GenBound0002
  | ⟨3, _⟩ => plane292GenBound0003
  | ⟨4, _⟩ => plane292GenBound0004
  | ⟨5, _⟩ => plane292GenBound0005
  | ⟨6, _⟩ => plane292GenBound0006
  | ⟨7, _⟩ => plane292GenBound0007
  | ⟨8, _⟩ => plane292GenBound0008
  | ⟨9, _⟩ => plane292GenBound0009
  | ⟨10, _⟩ => plane292GenBound0010
  | ⟨11, _⟩ => plane292GenBound0011
  | ⟨12, _⟩ => plane292GenBound0012
  | ⟨13, _⟩ => plane292GenBound0013
  | ⟨14, _⟩ => plane292GenBound0014
  | ⟨15, _⟩ => plane292GenBound0015
  | ⟨16, _⟩ => plane292GenBound0016
  | ⟨17, _⟩ => plane292GenBound0017
  | ⟨18, _⟩ => plane292GenBound0018
  | ⟨19, _⟩ => plane292GenBound0019
  | ⟨20, _⟩ => plane292GenBound0020
  | ⟨21, _⟩ => plane292GenBound0021
  | ⟨22, _⟩ => plane292GenBound0022
  | ⟨23, _⟩ => plane292GenBound0023
  | ⟨24, _⟩ => plane292GenBound0024
  | ⟨25, _⟩ => plane292GenBound0025
  | ⟨26, _⟩ => plane292GenBound0026
  | ⟨27, _⟩ => plane292GenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane292GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (0 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (0 : Fin 20) = [128, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0000 (by decide)
theorem plane292GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (1 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (1 : Fin 20) = [128, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0001 (by decide)
theorem plane292GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (2 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (2 : Fin 20) = [128, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0002 (by decide)
theorem plane292GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (3 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (3 : Fin 20) = [128, 70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0003 (by decide)
theorem plane292GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (4 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (4 : Fin 20) = [128, 80, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0004 (by decide)
theorem plane292GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (5 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (5 : Fin 20) = [128, 82, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0005 (by decide)
theorem plane292GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (6 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (6 : Fin 20) = [128, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0006 (by decide)
theorem plane292GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (7 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (7 : Fin 20) = [128, 86, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0007 (by decide)
theorem plane292GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (8 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (8 : Fin 20) = [258, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0008 (by decide)
theorem plane292GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (9 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (9 : Fin 20) = [262, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0009 (by decide)
theorem plane292GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (10 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (10 : Fin 20) = [272, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0010 (by decide)
theorem plane292GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (11 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (11 : Fin 20) = [274, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0011 (by decide)
theorem plane292GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (12 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (12 : Fin 20) = [276, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0012 (by decide)
theorem plane292GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (13 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (13 : Fin 20) = [278, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0013 (by decide)
theorem plane292GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (14 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (14 : Fin 20) = [322, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0014 (by decide)
theorem plane292GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (15 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (15 : Fin 20) = [324, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0015 (by decide)
theorem plane292GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (16 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (16 : Fin 20) = [336, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0016 (by decide)
theorem plane292GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (17 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (17 : Fin 20) = [338, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0017 (by decide)
theorem plane292GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (18 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (18 : Fin 20) = [340, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0018 (by decide)
theorem plane292GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis (19 : Fin 20))) 15 := by
  rw [show plane292GenDeadBasis (19 : Fin 20) = [342, 128, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane292GenSource0019 (by decide)
theorem plane292GenDeadQRA (d : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane292GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane292GenDeadBound0000
  | ⟨1, _⟩ => plane292GenDeadBound0001
  | ⟨2, _⟩ => plane292GenDeadBound0002
  | ⟨3, _⟩ => plane292GenDeadBound0003
  | ⟨4, _⟩ => plane292GenDeadBound0004
  | ⟨5, _⟩ => plane292GenDeadBound0005
  | ⟨6, _⟩ => plane292GenDeadBound0006
  | ⟨7, _⟩ => plane292GenDeadBound0007
  | ⟨8, _⟩ => plane292GenDeadBound0008
  | ⟨9, _⟩ => plane292GenDeadBound0009
  | ⟨10, _⟩ => plane292GenDeadBound0010
  | ⟨11, _⟩ => plane292GenDeadBound0011
  | ⟨12, _⟩ => plane292GenDeadBound0012
  | ⟨13, _⟩ => plane292GenDeadBound0013
  | ⟨14, _⟩ => plane292GenDeadBound0014
  | ⟨15, _⟩ => plane292GenDeadBound0015
  | ⟨16, _⟩ => plane292GenDeadBound0016
  | ⟨17, _⟩ => plane292GenDeadBound0017
  | ⟨18, _⟩ => plane292GenDeadBound0018
  | ⟨19, _⟩ => plane292GenDeadBound0019
  | ⟨k + 20, h⟩ => by omega
end QiushiMatmul
