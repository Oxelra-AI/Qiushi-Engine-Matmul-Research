import QiushiPlane267GenBindings00
import QiushiPlane267GenBindings01
import QiushiPlane267GenBindings02
import QiushiPlane267GenBindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane267GenSourceQRA (i : Fin 33) :
    QuotientRankAtLeast (spanCodes (plane267GenSourceBasis i)) (plane267GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane267GenBound0000
  | ⟨1, _⟩ => plane267GenBound0001
  | ⟨2, _⟩ => plane267GenBound0002
  | ⟨3, _⟩ => plane267GenBound0003
  | ⟨4, _⟩ => plane267GenBound0004
  | ⟨5, _⟩ => plane267GenBound0005
  | ⟨6, _⟩ => plane267GenBound0006
  | ⟨7, _⟩ => plane267GenBound0007
  | ⟨8, _⟩ => plane267GenBound0008
  | ⟨9, _⟩ => plane267GenBound0009
  | ⟨10, _⟩ => plane267GenBound0010
  | ⟨11, _⟩ => plane267GenBound0011
  | ⟨12, _⟩ => plane267GenBound0012
  | ⟨13, _⟩ => plane267GenBound0013
  | ⟨14, _⟩ => plane267GenBound0014
  | ⟨15, _⟩ => plane267GenBound0015
  | ⟨16, _⟩ => plane267GenBound0016
  | ⟨17, _⟩ => plane267GenBound0017
  | ⟨18, _⟩ => plane267GenBound0018
  | ⟨19, _⟩ => plane267GenBound0019
  | ⟨20, _⟩ => plane267GenBound0020
  | ⟨21, _⟩ => plane267GenBound0021
  | ⟨22, _⟩ => plane267GenBound0022
  | ⟨23, _⟩ => plane267GenBound0023
  | ⟨24, _⟩ => plane267GenBound0024
  | ⟨25, _⟩ => plane267GenBound0025
  | ⟨26, _⟩ => plane267GenBound0026
  | ⟨27, _⟩ => plane267GenBound0027
  | ⟨28, _⟩ => plane267GenBound0028
  | ⟨29, _⟩ => plane267GenBound0029
  | ⟨30, _⟩ => plane267GenBound0030
  | ⟨31, _⟩ => plane267GenBound0031
  | ⟨32, _⟩ => plane267GenBound0032
  | ⟨k + 33, h⟩ => by omega
theorem plane267GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (0 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (0 : Fin 11) = [84, 32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0000 (by decide)
theorem plane267GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (1 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (1 : Fin 11) = [68, 32, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0001 (by decide)
theorem plane267GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (2 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (2 : Fin 11) = [76, 32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0002 (by decide)
theorem plane267GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (3 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (3 : Fin 11) = [132, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0003 (by decide)
theorem plane267GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (4 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (4 : Fin 11) = [136, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0004 (by decide)
theorem plane267GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (5 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (5 : Fin 11) = [152, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0005 (by decide)
theorem plane267GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (6 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (6 : Fin 11) = [156, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0006 (by decide)
theorem plane267GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (7 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (7 : Fin 11) = [264, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0007 (by decide)
theorem plane267GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (8 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (8 : Fin 11) = [268, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0008 (by decide)
theorem plane267GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (9 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (9 : Fin 11) = [408, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0009 (by decide)
theorem plane267GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis (10 : Fin 11))) 15 := by
  rw [show plane267GenDeadBasis (10 : Fin 11) = [412, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane267GenSource0010 (by decide)
theorem plane267GenDeadQRA (d : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane267GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane267GenDeadBound0000
  | ⟨1, _⟩ => plane267GenDeadBound0001
  | ⟨2, _⟩ => plane267GenDeadBound0002
  | ⟨3, _⟩ => plane267GenDeadBound0003
  | ⟨4, _⟩ => plane267GenDeadBound0004
  | ⟨5, _⟩ => plane267GenDeadBound0005
  | ⟨6, _⟩ => plane267GenDeadBound0006
  | ⟨7, _⟩ => plane267GenDeadBound0007
  | ⟨8, _⟩ => plane267GenDeadBound0008
  | ⟨9, _⟩ => plane267GenDeadBound0009
  | ⟨10, _⟩ => plane267GenDeadBound0010
  | ⟨k + 11, h⟩ => by omega
end QiushiMatmul
