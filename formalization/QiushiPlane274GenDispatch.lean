import QiushiPlane274GenBindings00
import QiushiPlane274GenBindings01
import QiushiPlane274GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane274GenSourceQRA (i : Fin 29) :
    QuotientRankAtLeast (spanCodes (plane274GenSourceBasis i)) (plane274GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane274GenBound0000
  | ⟨1, _⟩ => plane274GenBound0001
  | ⟨2, _⟩ => plane274GenBound0002
  | ⟨3, _⟩ => plane274GenBound0003
  | ⟨4, _⟩ => plane274GenBound0004
  | ⟨5, _⟩ => plane274GenBound0005
  | ⟨6, _⟩ => plane274GenBound0006
  | ⟨7, _⟩ => plane274GenBound0007
  | ⟨8, _⟩ => plane274GenBound0008
  | ⟨9, _⟩ => plane274GenBound0009
  | ⟨10, _⟩ => plane274GenBound0010
  | ⟨11, _⟩ => plane274GenBound0011
  | ⟨12, _⟩ => plane274GenBound0012
  | ⟨13, _⟩ => plane274GenBound0013
  | ⟨14, _⟩ => plane274GenBound0014
  | ⟨15, _⟩ => plane274GenBound0015
  | ⟨16, _⟩ => plane274GenBound0016
  | ⟨17, _⟩ => plane274GenBound0017
  | ⟨18, _⟩ => plane274GenBound0018
  | ⟨19, _⟩ => plane274GenBound0019
  | ⟨20, _⟩ => plane274GenBound0020
  | ⟨21, _⟩ => plane274GenBound0021
  | ⟨22, _⟩ => plane274GenBound0022
  | ⟨23, _⟩ => plane274GenBound0023
  | ⟨24, _⟩ => plane274GenBound0024
  | ⟨25, _⟩ => plane274GenBound0025
  | ⟨26, _⟩ => plane274GenBound0026
  | ⟨27, _⟩ => plane274GenBound0027
  | ⟨28, _⟩ => plane274GenBound0028
  | ⟨k + 29, h⟩ => by omega
theorem plane274GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (0 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (0 : Fin 10) = [160, 80, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0000 (by decide)
theorem plane274GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (1 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (1 : Fin 10) = [160, 80, 12, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0001 (by decide)
theorem plane274GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (2 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (2 : Fin 10) = [160, 64, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0002 (by decide)
theorem plane274GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (3 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (3 : Fin 10) = [160, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0003 (by decide)
theorem plane274GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (4 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (4 : Fin 10) = [160, 72, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0004 (by decide)
theorem plane274GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (5 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (5 : Fin 10) = [160, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0005 (by decide)
theorem plane274GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (6 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (6 : Fin 10) = [132, 80, 36, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0006 (by decide)
theorem plane274GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (7 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (7 : Fin 10) = [140, 80, 44, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0007 (by decide)
theorem plane274GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (8 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (8 : Fin 10) = [148, 80, 52, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0008 (by decide)
theorem plane274GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis (9 : Fin 10))) 15 := by
  rw [show plane274GenDeadBasis (9 : Fin 10) = [156, 80, 60, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane274GenSource0009 (by decide)
theorem plane274GenDeadQRA (d : Fin 10) :
    QuotientRankAtLeast (spanCodes (plane274GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane274GenDeadBound0000
  | ⟨1, _⟩ => plane274GenDeadBound0001
  | ⟨2, _⟩ => plane274GenDeadBound0002
  | ⟨3, _⟩ => plane274GenDeadBound0003
  | ⟨4, _⟩ => plane274GenDeadBound0004
  | ⟨5, _⟩ => plane274GenDeadBound0005
  | ⟨6, _⟩ => plane274GenDeadBound0006
  | ⟨7, _⟩ => plane274GenDeadBound0007
  | ⟨8, _⟩ => plane274GenDeadBound0008
  | ⟨9, _⟩ => plane274GenDeadBound0009
  | ⟨k + 10, h⟩ => by omega
end QiushiMatmul
