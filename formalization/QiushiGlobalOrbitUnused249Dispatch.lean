import QiushiGlobalOrbitUnused249Bindings00
import QiushiGlobalOrbitUnused249Bindings01
import QiushiGlobalOrbitUnused249Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane249UnusedGenSourceQRA (i : Fin 29) :
    QuotientRankAtLeast (spanCodes (plane249UnusedGenSourceBasis i)) (plane249UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane249UnusedGenBound0000
  | ⟨1, _⟩ => plane249UnusedGenBound0001
  | ⟨2, _⟩ => plane249UnusedGenBound0002
  | ⟨3, _⟩ => plane249UnusedGenBound0003
  | ⟨4, _⟩ => plane249UnusedGenBound0004
  | ⟨5, _⟩ => plane249UnusedGenBound0005
  | ⟨6, _⟩ => plane249UnusedGenBound0006
  | ⟨7, _⟩ => plane249UnusedGenBound0007
  | ⟨8, _⟩ => plane249UnusedGenBound0008
  | ⟨9, _⟩ => plane249UnusedGenBound0009
  | ⟨10, _⟩ => plane249UnusedGenBound0010
  | ⟨11, _⟩ => plane249UnusedGenBound0011
  | ⟨12, _⟩ => plane249UnusedGenBound0012
  | ⟨13, _⟩ => plane249UnusedGenBound0013
  | ⟨14, _⟩ => plane249UnusedGenBound0014
  | ⟨15, _⟩ => plane249UnusedGenBound0015
  | ⟨16, _⟩ => plane249UnusedGenBound0016
  | ⟨17, _⟩ => plane249UnusedGenBound0017
  | ⟨18, _⟩ => plane249UnusedGenBound0018
  | ⟨19, _⟩ => plane249UnusedGenBound0019
  | ⟨20, _⟩ => plane249UnusedGenBound0020
  | ⟨21, _⟩ => plane249UnusedGenBound0021
  | ⟨22, _⟩ => plane249UnusedGenBound0022
  | ⟨23, _⟩ => plane249UnusedGenBound0023
  | ⟨24, _⟩ => plane249UnusedGenBound0024
  | ⟨25, _⟩ => plane249UnusedGenBound0025
  | ⟨26, _⟩ => plane249UnusedGenBound0026
  | ⟨27, _⟩ => plane249UnusedGenBound0027
  | ⟨28, _⟩ => plane249UnusedGenBound0028
  | ⟨k + 29, h⟩ => by omega
theorem plane249UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane249UnusedGenDeadBasis (0 : Fin 3))) 13 := by
  rw [show plane249UnusedGenDeadBasis (0 : Fin 3) = [80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane249UnusedGenSource0000 (by decide)
theorem plane249UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane249UnusedGenDeadBasis (1 : Fin 3))) 13 := by
  rw [show plane249UnusedGenDeadBasis (1 : Fin 3) = [128, 80, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane249UnusedGenSource0001 (by decide)
theorem plane249UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane249UnusedGenDeadBasis (2 : Fin 3))) 13 := by
  rw [show plane249UnusedGenDeadBasis (2 : Fin 3) = [136, 80, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane249UnusedGenSource0002 (by decide)
theorem plane249UnusedGenDeadQRA (d : Fin 3) :
    QuotientRankAtLeast (spanCodes (plane249UnusedGenDeadBasis d)) 13 :=
  match d with
  | ⟨0, _⟩ => plane249UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane249UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane249UnusedGenDeadBound0002
  | ⟨k + 3, h⟩ => by omega
end QiushiMatmul
