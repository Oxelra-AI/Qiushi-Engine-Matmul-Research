import QiushiPlane269GenBindings00
import QiushiPlane269GenBindings01
import QiushiPlane269GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane269GenSourceQRA (i : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane269GenSourceBasis i)) (plane269GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane269GenBound0000
  | ⟨1, _⟩ => plane269GenBound0001
  | ⟨2, _⟩ => plane269GenBound0002
  | ⟨3, _⟩ => plane269GenBound0003
  | ⟨4, _⟩ => plane269GenBound0004
  | ⟨5, _⟩ => plane269GenBound0005
  | ⟨6, _⟩ => plane269GenBound0006
  | ⟨7, _⟩ => plane269GenBound0007
  | ⟨8, _⟩ => plane269GenBound0008
  | ⟨9, _⟩ => plane269GenBound0009
  | ⟨10, _⟩ => plane269GenBound0010
  | ⟨11, _⟩ => plane269GenBound0011
  | ⟨12, _⟩ => plane269GenBound0012
  | ⟨13, _⟩ => plane269GenBound0013
  | ⟨14, _⟩ => plane269GenBound0014
  | ⟨15, _⟩ => plane269GenBound0015
  | ⟨16, _⟩ => plane269GenBound0016
  | ⟨17, _⟩ => plane269GenBound0017
  | ⟨18, _⟩ => plane269GenBound0018
  | ⟨19, _⟩ => plane269GenBound0019
  | ⟨20, _⟩ => plane269GenBound0020
  | ⟨21, _⟩ => plane269GenBound0021
  | ⟨22, _⟩ => plane269GenBound0022
  | ⟨23, _⟩ => plane269GenBound0023
  | ⟨24, _⟩ => plane269GenBound0024
  | ⟨25, _⟩ => plane269GenBound0025
  | ⟨26, _⟩ => plane269GenBound0026
  | ⟨27, _⟩ => plane269GenBound0027
  | ⟨28, _⟩ => plane269GenBound0028
  | ⟨29, _⟩ => plane269GenBound0029
  | ⟨k + 30, h⟩ => by omega
theorem plane269GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (0 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (0 : Fin 10) = [264, 32, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0000 (by decide)
theorem plane269GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (1 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (1 : Fin 10) = [264, 32, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0001 (by decide)
theorem plane269GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (2 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (2 : Fin 10) = [264, 32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0002 (by decide)
theorem plane269GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (3 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (3 : Fin 10) = [264, 32, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0003 (by decide)
theorem plane269GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (4 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (4 : Fin 10) = [264, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0004 (by decide)
theorem plane269GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (5 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (5 : Fin 10) = [264, 92, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0005 (by decide)
theorem plane269GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (6 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (6 : Fin 10) = [264, 132, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0006 (by decide)
theorem plane269GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (7 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (7 : Fin 10) = [264, 148, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0007 (by decide)
theorem plane269GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (8 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (8 : Fin 10) = [264, 196, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0008 (by decide)
theorem plane269GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis (9 : Fin 10))) 15 := by
  rw [show plane269GenDeadBasis (9 : Fin 10) = [264, 220, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane269GenSource0009 (by decide)
theorem plane269GenDeadQRA (d : Fin 10) :
    QuotientRankAtLeast (spanCodes (plane269GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane269GenDeadBound0000
  | ⟨1, _⟩ => plane269GenDeadBound0001
  | ⟨2, _⟩ => plane269GenDeadBound0002
  | ⟨3, _⟩ => plane269GenDeadBound0003
  | ⟨4, _⟩ => plane269GenDeadBound0004
  | ⟨5, _⟩ => plane269GenDeadBound0005
  | ⟨6, _⟩ => plane269GenDeadBound0006
  | ⟨7, _⟩ => plane269GenDeadBound0007
  | ⟨8, _⟩ => plane269GenDeadBound0008
  | ⟨9, _⟩ => plane269GenDeadBound0009
  | ⟨k + 10, h⟩ => by omega
end QiushiMatmul
