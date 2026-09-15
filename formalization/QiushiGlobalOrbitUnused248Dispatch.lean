import QiushiGlobalOrbitUnused248Bindings00
import QiushiGlobalOrbitUnused248Bindings01
import QiushiGlobalOrbitUnused248Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane248UnusedGenSourceQRA (i : Fin 23) :
    QuotientRankAtLeast (spanCodes (plane248UnusedGenSourceBasis i)) (plane248UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane248UnusedGenBound0000
  | ⟨1, _⟩ => plane248UnusedGenBound0001
  | ⟨2, _⟩ => plane248UnusedGenBound0002
  | ⟨3, _⟩ => plane248UnusedGenBound0003
  | ⟨4, _⟩ => plane248UnusedGenBound0004
  | ⟨5, _⟩ => plane248UnusedGenBound0005
  | ⟨6, _⟩ => plane248UnusedGenBound0006
  | ⟨7, _⟩ => plane248UnusedGenBound0007
  | ⟨8, _⟩ => plane248UnusedGenBound0008
  | ⟨9, _⟩ => plane248UnusedGenBound0009
  | ⟨10, _⟩ => plane248UnusedGenBound0010
  | ⟨11, _⟩ => plane248UnusedGenBound0011
  | ⟨12, _⟩ => plane248UnusedGenBound0012
  | ⟨13, _⟩ => plane248UnusedGenBound0013
  | ⟨14, _⟩ => plane248UnusedGenBound0014
  | ⟨15, _⟩ => plane248UnusedGenBound0015
  | ⟨16, _⟩ => plane248UnusedGenBound0016
  | ⟨17, _⟩ => plane248UnusedGenBound0017
  | ⟨18, _⟩ => plane248UnusedGenBound0018
  | ⟨19, _⟩ => plane248UnusedGenBound0019
  | ⟨20, _⟩ => plane248UnusedGenBound0020
  | ⟨21, _⟩ => plane248UnusedGenBound0021
  | ⟨22, _⟩ => plane248UnusedGenBound0022
  | ⟨k + 23, h⟩ => by omega
theorem plane248UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane248UnusedGenDeadBasis (0 : Fin 3))) 13 := by
  rw [show plane248UnusedGenDeadBasis (0 : Fin 3) = [80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane248UnusedGenSource0000 (by decide)
theorem plane248UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane248UnusedGenDeadBasis (1 : Fin 3))) 13 := by
  rw [show plane248UnusedGenDeadBasis (1 : Fin 3) = [96, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane248UnusedGenSource0001 (by decide)
theorem plane248UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane248UnusedGenDeadBasis (2 : Fin 3))) 13 := by
  rw [show plane248UnusedGenDeadBasis (2 : Fin 3) = [112, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane248UnusedGenSource0002 (by decide)
theorem plane248UnusedGenDeadQRA (d : Fin 3) :
    QuotientRankAtLeast (spanCodes (plane248UnusedGenDeadBasis d)) 13 :=
  match d with
  | ⟨0, _⟩ => plane248UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane248UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane248UnusedGenDeadBound0002
  | ⟨k + 3, h⟩ => by omega
end QiushiMatmul
