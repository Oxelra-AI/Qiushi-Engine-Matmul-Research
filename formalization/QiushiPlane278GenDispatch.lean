import QiushiPlane278GenBindings00
import QiushiPlane278GenBindings01
import QiushiPlane278GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane278GenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane278GenSourceBasis i)) (plane278GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane278GenBound0000
  | ⟨1, _⟩ => plane278GenBound0001
  | ⟨2, _⟩ => plane278GenBound0002
  | ⟨3, _⟩ => plane278GenBound0003
  | ⟨4, _⟩ => plane278GenBound0004
  | ⟨5, _⟩ => plane278GenBound0005
  | ⟨6, _⟩ => plane278GenBound0006
  | ⟨7, _⟩ => plane278GenBound0007
  | ⟨8, _⟩ => plane278GenBound0008
  | ⟨9, _⟩ => plane278GenBound0009
  | ⟨10, _⟩ => plane278GenBound0010
  | ⟨11, _⟩ => plane278GenBound0011
  | ⟨12, _⟩ => plane278GenBound0012
  | ⟨13, _⟩ => plane278GenBound0013
  | ⟨14, _⟩ => plane278GenBound0014
  | ⟨15, _⟩ => plane278GenBound0015
  | ⟨16, _⟩ => plane278GenBound0016
  | ⟨17, _⟩ => plane278GenBound0017
  | ⟨18, _⟩ => plane278GenBound0018
  | ⟨19, _⟩ => plane278GenBound0019
  | ⟨20, _⟩ => plane278GenBound0020
  | ⟨21, _⟩ => plane278GenBound0021
  | ⟨22, _⟩ => plane278GenBound0022
  | ⟨23, _⟩ => plane278GenBound0023
  | ⟨24, _⟩ => plane278GenBound0024
  | ⟨25, _⟩ => plane278GenBound0025
  | ⟨26, _⟩ => plane278GenBound0026
  | ⟨27, _⟩ => plane278GenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane278GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (0 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (0 : Fin 8) = [304, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0000 (by decide)
theorem plane278GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (1 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (1 : Fin 8) = [276, 68, 36, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0001 (by decide)
theorem plane278GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (2 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (2 : Fin 8) = [284, 76, 44, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0002 (by decide)
theorem plane278GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (3 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (3 : Fin 8) = [304, 180, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0003 (by decide)
theorem plane278GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (4 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (4 : Fin 8) = [304, 172, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0004 (by decide)
theorem plane278GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (5 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (5 : Fin 8) = [304, 140, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0005 (by decide)
theorem plane278GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (6 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (6 : Fin 8) = [304, 156, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0006 (by decide)
theorem plane278GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis (7 : Fin 8))) 15 := by
  rw [show plane278GenDeadBasis (7 : Fin 8) = [276, 68, 36, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane278GenSource0026 (by decide)
theorem plane278GenDeadQRA (d : Fin 8) :
    QuotientRankAtLeast (spanCodes (plane278GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane278GenDeadBound0000
  | ⟨1, _⟩ => plane278GenDeadBound0001
  | ⟨2, _⟩ => plane278GenDeadBound0002
  | ⟨3, _⟩ => plane278GenDeadBound0003
  | ⟨4, _⟩ => plane278GenDeadBound0004
  | ⟨5, _⟩ => plane278GenDeadBound0005
  | ⟨6, _⟩ => plane278GenDeadBound0006
  | ⟨7, _⟩ => plane278GenDeadBound0007
  | ⟨k + 8, h⟩ => by omega
end QiushiMatmul
