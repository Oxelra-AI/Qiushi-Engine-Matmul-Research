import QiushiPlane295GenBindings00
import QiushiPlane295GenBindings01
import QiushiPlane295GenBindings02
import QiushiPlane295GenBindings03
import QiushiPlane295GenBindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane295GenSourceQRA (i : Fin 46) :
    QuotientRankAtLeast (spanCodes (plane295GenSourceBasis i)) (plane295GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane295GenBound0000
  | ⟨1, _⟩ => plane295GenBound0001
  | ⟨2, _⟩ => plane295GenBound0002
  | ⟨3, _⟩ => plane295GenBound0003
  | ⟨4, _⟩ => plane295GenBound0004
  | ⟨5, _⟩ => plane295GenBound0005
  | ⟨6, _⟩ => plane295GenBound0006
  | ⟨7, _⟩ => plane295GenBound0007
  | ⟨8, _⟩ => plane295GenBound0008
  | ⟨9, _⟩ => plane295GenBound0009
  | ⟨10, _⟩ => plane295GenBound0010
  | ⟨11, _⟩ => plane295GenBound0011
  | ⟨12, _⟩ => plane295GenBound0012
  | ⟨13, _⟩ => plane295GenBound0013
  | ⟨14, _⟩ => plane295GenBound0014
  | ⟨15, _⟩ => plane295GenBound0015
  | ⟨16, _⟩ => plane295GenBound0016
  | ⟨17, _⟩ => plane295GenBound0017
  | ⟨18, _⟩ => plane295GenBound0018
  | ⟨19, _⟩ => plane295GenBound0019
  | ⟨20, _⟩ => plane295GenBound0020
  | ⟨21, _⟩ => plane295GenBound0021
  | ⟨22, _⟩ => plane295GenBound0022
  | ⟨23, _⟩ => plane295GenBound0023
  | ⟨24, _⟩ => plane295GenBound0024
  | ⟨25, _⟩ => plane295GenBound0025
  | ⟨26, _⟩ => plane295GenBound0026
  | ⟨27, _⟩ => plane295GenBound0027
  | ⟨28, _⟩ => plane295GenBound0028
  | ⟨29, _⟩ => plane295GenBound0029
  | ⟨30, _⟩ => plane295GenBound0030
  | ⟨31, _⟩ => plane295GenBound0031
  | ⟨32, _⟩ => plane295GenBound0032
  | ⟨33, _⟩ => plane295GenBound0033
  | ⟨34, _⟩ => plane295GenBound0034
  | ⟨35, _⟩ => plane295GenBound0035
  | ⟨36, _⟩ => plane295GenBound0036
  | ⟨37, _⟩ => plane295GenBound0037
  | ⟨38, _⟩ => plane295GenBound0038
  | ⟨39, _⟩ => plane295GenBound0039
  | ⟨40, _⟩ => plane295GenBound0040
  | ⟨41, _⟩ => plane295GenBound0041
  | ⟨42, _⟩ => plane295GenBound0042
  | ⟨43, _⟩ => plane295GenBound0043
  | ⟨44, _⟩ => plane295GenBound0044
  | ⟨45, _⟩ => plane295GenBound0045
  | ⟨k + 46, h⟩ => by omega
theorem plane295GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (0 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (0 : Fin 7) = [262, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0000 (by decide)
theorem plane295GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (1 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (1 : Fin 7) = [272, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0001 (by decide)
theorem plane295GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (2 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (2 : Fin 7) = [272, 70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0002 (by decide)
theorem plane295GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (3 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (3 : Fin 7) = [272, 132, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0003 (by decide)
theorem plane295GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (4 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (4 : Fin 7) = [272, 148, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0004 (by decide)
theorem plane295GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (5 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (5 : Fin 7) = [272, 198, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0005 (by decide)
theorem plane295GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis (6 : Fin 7))) 16 := by
  rw [show plane295GenDeadBasis (6 : Fin 7) = [272, 212, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane295GenSource0006 (by decide)
theorem plane295GenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane295GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane295GenDeadBound0000
  | ⟨1, _⟩ => plane295GenDeadBound0001
  | ⟨2, _⟩ => plane295GenDeadBound0002
  | ⟨3, _⟩ => plane295GenDeadBound0003
  | ⟨4, _⟩ => plane295GenDeadBound0004
  | ⟨5, _⟩ => plane295GenDeadBound0005
  | ⟨6, _⟩ => plane295GenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
