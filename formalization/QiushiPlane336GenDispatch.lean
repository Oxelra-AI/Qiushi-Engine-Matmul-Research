import QiushiPlane336GenBindings00
import QiushiPlane336GenBindings01
import QiushiPlane336GenBindings02
import QiushiPlane336GenBindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane336GenSourceQRA (i : Fin 34) :
    QuotientRankAtLeast (spanCodes (plane336GenSourceBasis i)) (plane336GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane336GenBound0000
  | ⟨1, _⟩ => plane336GenBound0001
  | ⟨2, _⟩ => plane336GenBound0002
  | ⟨3, _⟩ => plane336GenBound0003
  | ⟨4, _⟩ => plane336GenBound0004
  | ⟨5, _⟩ => plane336GenBound0005
  | ⟨6, _⟩ => plane336GenBound0006
  | ⟨7, _⟩ => plane336GenBound0007
  | ⟨8, _⟩ => plane336GenBound0008
  | ⟨9, _⟩ => plane336GenBound0009
  | ⟨10, _⟩ => plane336GenBound0010
  | ⟨11, _⟩ => plane336GenBound0011
  | ⟨12, _⟩ => plane336GenBound0012
  | ⟨13, _⟩ => plane336GenBound0013
  | ⟨14, _⟩ => plane336GenBound0014
  | ⟨15, _⟩ => plane336GenBound0015
  | ⟨16, _⟩ => plane336GenBound0016
  | ⟨17, _⟩ => plane336GenBound0017
  | ⟨18, _⟩ => plane336GenBound0018
  | ⟨19, _⟩ => plane336GenBound0019
  | ⟨20, _⟩ => plane336GenBound0020
  | ⟨21, _⟩ => plane336GenBound0021
  | ⟨22, _⟩ => plane336GenBound0022
  | ⟨23, _⟩ => plane336GenBound0023
  | ⟨24, _⟩ => plane336GenBound0024
  | ⟨25, _⟩ => plane336GenBound0025
  | ⟨26, _⟩ => plane336GenBound0026
  | ⟨27, _⟩ => plane336GenBound0027
  | ⟨28, _⟩ => plane336GenBound0028
  | ⟨29, _⟩ => plane336GenBound0029
  | ⟨30, _⟩ => plane336GenBound0030
  | ⟨31, _⟩ => plane336GenBound0031
  | ⟨32, _⟩ => plane336GenBound0032
  | ⟨33, _⟩ => plane336GenBound0033
  | ⟨k + 34, h⟩ => by omega
theorem plane336GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (0 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (0 : Fin 13) = [256, 98, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0000 (by decide)
theorem plane336GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (1 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (1 : Fin 13) = [256, 98, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0001 (by decide)
theorem plane336GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (2 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (2 : Fin 13) = [256, 76, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0002 (by decide)
theorem plane336GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (3 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (3 : Fin 13) = [256, 132, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0003 (by decide)
theorem plane336GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (4 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (4 : Fin 13) = [256, 136, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0004 (by decide)
theorem plane336GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (5 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (5 : Fin 13) = [256, 138, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0005 (by decide)
theorem plane336GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (6 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (6 : Fin 13) = [256, 140, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0006 (by decide)
theorem plane336GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (7 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (7 : Fin 13) = [256, 142, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0007 (by decide)
theorem plane336GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (8 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (8 : Fin 13) = [256, 164, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0008 (by decide)
theorem plane336GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (9 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (9 : Fin 13) = [256, 166, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0009 (by decide)
theorem plane336GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (10 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (10 : Fin 13) = [256, 168, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0010 (by decide)
theorem plane336GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (11 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (11 : Fin 13) = [256, 172, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0011 (by decide)
theorem plane336GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis (12 : Fin 13))) 15 := by
  rw [show plane336GenDeadBasis (12 : Fin 13) = [256, 174, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane336GenSource0012 (by decide)
theorem plane336GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane336GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane336GenDeadBound0000
  | ⟨1, _⟩ => plane336GenDeadBound0001
  | ⟨2, _⟩ => plane336GenDeadBound0002
  | ⟨3, _⟩ => plane336GenDeadBound0003
  | ⟨4, _⟩ => plane336GenDeadBound0004
  | ⟨5, _⟩ => plane336GenDeadBound0005
  | ⟨6, _⟩ => plane336GenDeadBound0006
  | ⟨7, _⟩ => plane336GenDeadBound0007
  | ⟨8, _⟩ => plane336GenDeadBound0008
  | ⟨9, _⟩ => plane336GenDeadBound0009
  | ⟨10, _⟩ => plane336GenDeadBound0010
  | ⟨11, _⟩ => plane336GenDeadBound0011
  | ⟨12, _⟩ => plane336GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
