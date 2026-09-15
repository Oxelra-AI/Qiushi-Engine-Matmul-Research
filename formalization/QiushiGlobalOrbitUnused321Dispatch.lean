import QiushiGlobalOrbitUnused321Bindings00
import QiushiGlobalOrbitUnused321Bindings01
import QiushiGlobalOrbitUnused321Bindings02
import QiushiGlobalOrbitUnused321Bindings03
import QiushiGlobalOrbitUnused321Bindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane321UnusedGenSourceQRA (i : Fin 49) :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenSourceBasis i)) (plane321UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane321UnusedGenBound0000
  | ⟨1, _⟩ => plane321UnusedGenBound0001
  | ⟨2, _⟩ => plane321UnusedGenBound0002
  | ⟨3, _⟩ => plane321UnusedGenBound0003
  | ⟨4, _⟩ => plane321UnusedGenBound0004
  | ⟨5, _⟩ => plane321UnusedGenBound0005
  | ⟨6, _⟩ => plane321UnusedGenBound0006
  | ⟨7, _⟩ => plane321UnusedGenBound0007
  | ⟨8, _⟩ => plane321UnusedGenBound0008
  | ⟨9, _⟩ => plane321UnusedGenBound0009
  | ⟨10, _⟩ => plane321UnusedGenBound0010
  | ⟨11, _⟩ => plane321UnusedGenBound0011
  | ⟨12, _⟩ => plane321UnusedGenBound0012
  | ⟨13, _⟩ => plane321UnusedGenBound0013
  | ⟨14, _⟩ => plane321UnusedGenBound0014
  | ⟨15, _⟩ => plane321UnusedGenBound0015
  | ⟨16, _⟩ => plane321UnusedGenBound0016
  | ⟨17, _⟩ => plane321UnusedGenBound0017
  | ⟨18, _⟩ => plane321UnusedGenBound0018
  | ⟨19, _⟩ => plane321UnusedGenBound0019
  | ⟨20, _⟩ => plane321UnusedGenBound0020
  | ⟨21, _⟩ => plane321UnusedGenBound0021
  | ⟨22, _⟩ => plane321UnusedGenBound0022
  | ⟨23, _⟩ => plane321UnusedGenBound0023
  | ⟨24, _⟩ => plane321UnusedGenBound0024
  | ⟨25, _⟩ => plane321UnusedGenBound0025
  | ⟨26, _⟩ => plane321UnusedGenBound0026
  | ⟨27, _⟩ => plane321UnusedGenBound0027
  | ⟨28, _⟩ => plane321UnusedGenBound0028
  | ⟨29, _⟩ => plane321UnusedGenBound0029
  | ⟨30, _⟩ => plane321UnusedGenBound0030
  | ⟨31, _⟩ => plane321UnusedGenBound0031
  | ⟨32, _⟩ => plane321UnusedGenBound0032
  | ⟨33, _⟩ => plane321UnusedGenBound0033
  | ⟨34, _⟩ => plane321UnusedGenBound0034
  | ⟨35, _⟩ => plane321UnusedGenBound0035
  | ⟨36, _⟩ => plane321UnusedGenBound0036
  | ⟨37, _⟩ => plane321UnusedGenBound0037
  | ⟨38, _⟩ => plane321UnusedGenBound0038
  | ⟨39, _⟩ => plane321UnusedGenBound0039
  | ⟨40, _⟩ => plane321UnusedGenBound0040
  | ⟨41, _⟩ => plane321UnusedGenBound0041
  | ⟨42, _⟩ => plane321UnusedGenBound0042
  | ⟨43, _⟩ => plane321UnusedGenBound0043
  | ⟨44, _⟩ => plane321UnusedGenBound0044
  | ⟨45, _⟩ => plane321UnusedGenBound0045
  | ⟨46, _⟩ => plane321UnusedGenBound0046
  | ⟨47, _⟩ => plane321UnusedGenBound0047
  | ⟨48, _⟩ => plane321UnusedGenBound0048
  | ⟨k + 49, h⟩ => by omega
theorem plane321UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis (0 : Fin 5))) 16 := by
  rw [show plane321UnusedGenDeadBasis (0 : Fin 5) = [290, 160, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane321UnusedGenSource0000 (by decide)
theorem plane321UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis (1 : Fin 5))) 16 := by
  rw [show plane321UnusedGenDeadBasis (1 : Fin 5) = [306, 160, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane321UnusedGenSource0001 (by decide)
theorem plane321UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis (2 : Fin 5))) 16 := by
  rw [show plane321UnusedGenDeadBasis (2 : Fin 5) = [306, 160, 70, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane321UnusedGenSource0002 (by decide)
theorem plane321UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis (3 : Fin 5))) 16 := by
  rw [show plane321UnusedGenDeadBasis (3 : Fin 5) = [306, 160, 100, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane321UnusedGenSource0003 (by decide)
theorem plane321UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis (4 : Fin 5))) 16 := by
  rw [show plane321UnusedGenDeadBasis (4 : Fin 5) = [306, 160, 116, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane321UnusedGenSource0004 (by decide)
theorem plane321UnusedGenDeadQRA (d : Fin 5) :
    QuotientRankAtLeast (spanCodes (plane321UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane321UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane321UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane321UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane321UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane321UnusedGenDeadBound0004
  | ⟨k + 5, h⟩ => by omega
end QiushiMatmul
