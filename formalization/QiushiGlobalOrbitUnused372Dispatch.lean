import QiushiGlobalOrbitUnused372Bindings00
import QiushiGlobalOrbitUnused372Bindings01
import QiushiGlobalOrbitUnused372Bindings02
import QiushiGlobalOrbitUnused372Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane372UnusedGenSourceQRA (i : Fin 37) :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenSourceBasis i)) (plane372UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane372UnusedGenBound0000
  | ⟨1, _⟩ => plane372UnusedGenBound0001
  | ⟨2, _⟩ => plane372UnusedGenBound0002
  | ⟨3, _⟩ => plane372UnusedGenBound0003
  | ⟨4, _⟩ => plane372UnusedGenBound0004
  | ⟨5, _⟩ => plane372UnusedGenBound0005
  | ⟨6, _⟩ => plane372UnusedGenBound0006
  | ⟨7, _⟩ => plane372UnusedGenBound0007
  | ⟨8, _⟩ => plane372UnusedGenBound0008
  | ⟨9, _⟩ => plane372UnusedGenBound0009
  | ⟨10, _⟩ => plane372UnusedGenBound0010
  | ⟨11, _⟩ => plane372UnusedGenBound0011
  | ⟨12, _⟩ => plane372UnusedGenBound0012
  | ⟨13, _⟩ => plane372UnusedGenBound0013
  | ⟨14, _⟩ => plane372UnusedGenBound0014
  | ⟨15, _⟩ => plane372UnusedGenBound0015
  | ⟨16, _⟩ => plane372UnusedGenBound0016
  | ⟨17, _⟩ => plane372UnusedGenBound0017
  | ⟨18, _⟩ => plane372UnusedGenBound0018
  | ⟨19, _⟩ => plane372UnusedGenBound0019
  | ⟨20, _⟩ => plane372UnusedGenBound0020
  | ⟨21, _⟩ => plane372UnusedGenBound0021
  | ⟨22, _⟩ => plane372UnusedGenBound0022
  | ⟨23, _⟩ => plane372UnusedGenBound0023
  | ⟨24, _⟩ => plane372UnusedGenBound0024
  | ⟨25, _⟩ => plane372UnusedGenBound0025
  | ⟨26, _⟩ => plane372UnusedGenBound0026
  | ⟨27, _⟩ => plane372UnusedGenBound0027
  | ⟨28, _⟩ => plane372UnusedGenBound0028
  | ⟨29, _⟩ => plane372UnusedGenBound0029
  | ⟨30, _⟩ => plane372UnusedGenBound0030
  | ⟨31, _⟩ => plane372UnusedGenBound0031
  | ⟨32, _⟩ => plane372UnusedGenBound0032
  | ⟨33, _⟩ => plane372UnusedGenBound0033
  | ⟨34, _⟩ => plane372UnusedGenBound0034
  | ⟨35, _⟩ => plane372UnusedGenBound0035
  | ⟨36, _⟩ => plane372UnusedGenBound0036
  | ⟨k + 37, h⟩ => by omega
theorem plane372UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis (0 : Fin 5))) 16 := by
  rw [show plane372UnusedGenDeadBasis (0 : Fin 5) = [258, 200, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane372UnusedGenSource0003 (by decide)
theorem plane372UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis (1 : Fin 5))) 16 := by
  rw [show plane372UnusedGenDeadBasis (1 : Fin 5) = [298, 164, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane372UnusedGenSource0006 (by decide)
theorem plane372UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis (2 : Fin 5))) 16 := by
  rw [show plane372UnusedGenDeadBasis (2 : Fin 5) = [298, 170, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane372UnusedGenSource0008 (by decide)
theorem plane372UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis (3 : Fin 5))) 16 := by
  rw [show plane372UnusedGenDeadBasis (3 : Fin 5) = [298, 174, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane372UnusedGenSource0009 (by decide)
theorem plane372UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis (4 : Fin 5))) 16 := by
  rw [show plane372UnusedGenDeadBasis (4 : Fin 5) = [298, 140, 108, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane372UnusedGenSource0010 (by decide)
theorem plane372UnusedGenDeadQRA (d : Fin 5) :
    QuotientRankAtLeast (spanCodes (plane372UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane372UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane372UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane372UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane372UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane372UnusedGenDeadBound0004
  | ⟨k + 5, h⟩ => by omega
end QiushiMatmul
