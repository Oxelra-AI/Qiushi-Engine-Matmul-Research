import QiushiPlane254GenBindings00
import QiushiPlane254GenBindings01
import QiushiPlane254GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane254GenSourceQRA (i : Fin 26) :
    QuotientRankAtLeast (spanCodes (plane254GenSourceBasis i)) (plane254GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane254GenBound0000
  | ⟨1, _⟩ => plane254GenBound0001
  | ⟨2, _⟩ => plane254GenBound0002
  | ⟨3, _⟩ => plane254GenBound0003
  | ⟨4, _⟩ => plane254GenBound0004
  | ⟨5, _⟩ => plane254GenBound0005
  | ⟨6, _⟩ => plane254GenBound0006
  | ⟨7, _⟩ => plane254GenBound0007
  | ⟨8, _⟩ => plane254GenBound0008
  | ⟨9, _⟩ => plane254GenBound0009
  | ⟨10, _⟩ => plane254GenBound0010
  | ⟨11, _⟩ => plane254GenBound0011
  | ⟨12, _⟩ => plane254GenBound0012
  | ⟨13, _⟩ => plane254GenBound0013
  | ⟨14, _⟩ => plane254GenBound0014
  | ⟨15, _⟩ => plane254GenBound0015
  | ⟨16, _⟩ => plane254GenBound0016
  | ⟨17, _⟩ => plane254GenBound0017
  | ⟨18, _⟩ => plane254GenBound0018
  | ⟨19, _⟩ => plane254GenBound0019
  | ⟨20, _⟩ => plane254GenBound0020
  | ⟨21, _⟩ => plane254GenBound0021
  | ⟨22, _⟩ => plane254GenBound0022
  | ⟨23, _⟩ => plane254GenBound0023
  | ⟨24, _⟩ => plane254GenBound0024
  | ⟨25, _⟩ => plane254GenBound0025
  | ⟨k + 26, h⟩ => by omega
theorem plane254GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (0 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (0 : Fin 13) = [68, 16, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0000 (by decide)
theorem plane254GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (1 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (1 : Fin 13) = [84, 32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0001 (by decide)
theorem plane254GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (2 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (2 : Fin 13) = [84, 36, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0002 (by decide)
theorem plane254GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (3 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (3 : Fin 13) = [84, 48, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0003 (by decide)
theorem plane254GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (4 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (4 : Fin 13) = [84, 52, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0004 (by decide)
theorem plane254GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (5 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (5 : Fin 13) = [128, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0005 (by decide)
theorem plane254GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (6 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (6 : Fin 13) = [132, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0006 (by decide)
theorem plane254GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (7 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (7 : Fin 13) = [144, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0007 (by decide)
theorem plane254GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (8 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (8 : Fin 13) = [148, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0008 (by decide)
theorem plane254GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (9 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (9 : Fin 13) = [160, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0009 (by decide)
theorem plane254GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (10 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (10 : Fin 13) = [164, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0010 (by decide)
theorem plane254GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (11 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (11 : Fin 13) = [176, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0011 (by decide)
theorem plane254GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis (12 : Fin 13))) 15 := by
  rw [show plane254GenDeadBasis (12 : Fin 13) = [180, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane254GenSource0012 (by decide)
theorem plane254GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane254GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane254GenDeadBound0000
  | ⟨1, _⟩ => plane254GenDeadBound0001
  | ⟨2, _⟩ => plane254GenDeadBound0002
  | ⟨3, _⟩ => plane254GenDeadBound0003
  | ⟨4, _⟩ => plane254GenDeadBound0004
  | ⟨5, _⟩ => plane254GenDeadBound0005
  | ⟨6, _⟩ => plane254GenDeadBound0006
  | ⟨7, _⟩ => plane254GenDeadBound0007
  | ⟨8, _⟩ => plane254GenDeadBound0008
  | ⟨9, _⟩ => plane254GenDeadBound0009
  | ⟨10, _⟩ => plane254GenDeadBound0010
  | ⟨11, _⟩ => plane254GenDeadBound0011
  | ⟨12, _⟩ => plane254GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
