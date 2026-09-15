import QiushiPlane276GenBindings00
import QiushiPlane276GenBindings01
import QiushiPlane276GenBindings02
import QiushiPlane276GenBindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane276GenSourceQRA (i : Fin 37) :
    QuotientRankAtLeast (spanCodes (plane276GenSourceBasis i)) (plane276GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane276GenBound0000
  | ⟨1, _⟩ => plane276GenBound0001
  | ⟨2, _⟩ => plane276GenBound0002
  | ⟨3, _⟩ => plane276GenBound0003
  | ⟨4, _⟩ => plane276GenBound0004
  | ⟨5, _⟩ => plane276GenBound0005
  | ⟨6, _⟩ => plane276GenBound0006
  | ⟨7, _⟩ => plane276GenBound0007
  | ⟨8, _⟩ => plane276GenBound0008
  | ⟨9, _⟩ => plane276GenBound0009
  | ⟨10, _⟩ => plane276GenBound0010
  | ⟨11, _⟩ => plane276GenBound0011
  | ⟨12, _⟩ => plane276GenBound0012
  | ⟨13, _⟩ => plane276GenBound0013
  | ⟨14, _⟩ => plane276GenBound0014
  | ⟨15, _⟩ => plane276GenBound0015
  | ⟨16, _⟩ => plane276GenBound0016
  | ⟨17, _⟩ => plane276GenBound0017
  | ⟨18, _⟩ => plane276GenBound0018
  | ⟨19, _⟩ => plane276GenBound0019
  | ⟨20, _⟩ => plane276GenBound0020
  | ⟨21, _⟩ => plane276GenBound0021
  | ⟨22, _⟩ => plane276GenBound0022
  | ⟨23, _⟩ => plane276GenBound0023
  | ⟨24, _⟩ => plane276GenBound0024
  | ⟨25, _⟩ => plane276GenBound0025
  | ⟨26, _⟩ => plane276GenBound0026
  | ⟨27, _⟩ => plane276GenBound0027
  | ⟨28, _⟩ => plane276GenBound0028
  | ⟨29, _⟩ => plane276GenBound0029
  | ⟨30, _⟩ => plane276GenBound0030
  | ⟨31, _⟩ => plane276GenBound0031
  | ⟨32, _⟩ => plane276GenBound0032
  | ⟨33, _⟩ => plane276GenBound0033
  | ⟨34, _⟩ => plane276GenBound0034
  | ⟨35, _⟩ => plane276GenBound0035
  | ⟨36, _⟩ => plane276GenBound0036
  | ⟨k + 37, h⟩ => by omega
theorem plane276GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (0 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (0 : Fin 17) = [272, 180, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0000 (by decide)
theorem plane276GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (1 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (1 : Fin 17) = [272, 92, 60, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0001 (by decide)
theorem plane276GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (2 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (2 : Fin 17) = [272, 140, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0002 (by decide)
theorem plane276GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (3 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (3 : Fin 17) = [272, 128, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0003 (by decide)
theorem plane276GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (4 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (4 : Fin 17) = [272, 96, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0004 (by decide)
theorem plane276GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (5 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (5 : Fin 17) = [272, 184, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0005 (by decide)
theorem plane276GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (6 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (6 : Fin 17) = [272, 68, 36, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0006 (by decide)
theorem plane276GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (7 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (7 : Fin 17) = [272, 164, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0007 (by decide)
theorem plane276GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (8 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (8 : Fin 17) = [260, 96, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0008 (by decide)
theorem plane276GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (9 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (9 : Fin 17) = [272, 148, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0009 (by decide)
theorem plane276GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (10 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (10 : Fin 17) = [268, 96, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0010 (by decide)
theorem plane276GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (11 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (11 : Fin 17) = [272, 76, 44, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0011 (by decide)
theorem plane276GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (12 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (12 : Fin 17) = [272, 156, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0012 (by decide)
theorem plane276GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (13 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (13 : Fin 17) = [272, 172, 96, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0013 (by decide)
theorem plane276GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (14 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (14 : Fin 17) = [260, 128, 96, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0034 (by decide)
theorem plane276GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (15 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (15 : Fin 17) = [272, 68, 36, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0035 (by decide)
theorem plane276GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis (16 : Fin 17))) 15 := by
  rw [show plane276GenDeadBasis (16 : Fin 17) = [268, 164, 96, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane276GenSource0036 (by decide)
theorem plane276GenDeadQRA (d : Fin 17) :
    QuotientRankAtLeast (spanCodes (plane276GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane276GenDeadBound0000
  | ⟨1, _⟩ => plane276GenDeadBound0001
  | ⟨2, _⟩ => plane276GenDeadBound0002
  | ⟨3, _⟩ => plane276GenDeadBound0003
  | ⟨4, _⟩ => plane276GenDeadBound0004
  | ⟨5, _⟩ => plane276GenDeadBound0005
  | ⟨6, _⟩ => plane276GenDeadBound0006
  | ⟨7, _⟩ => plane276GenDeadBound0007
  | ⟨8, _⟩ => plane276GenDeadBound0008
  | ⟨9, _⟩ => plane276GenDeadBound0009
  | ⟨10, _⟩ => plane276GenDeadBound0010
  | ⟨11, _⟩ => plane276GenDeadBound0011
  | ⟨12, _⟩ => plane276GenDeadBound0012
  | ⟨13, _⟩ => plane276GenDeadBound0013
  | ⟨14, _⟩ => plane276GenDeadBound0014
  | ⟨15, _⟩ => plane276GenDeadBound0015
  | ⟨16, _⟩ => plane276GenDeadBound0016
  | ⟨k + 17, h⟩ => by omega
end QiushiMatmul
