import QiushiPlane429GenBindings00
import QiushiPlane429GenBindings01
import QiushiPlane429GenBindings02
import QiushiPlane429GenBindings03
import QiushiPlane429GenBindings04
import QiushiPlane429GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane429GenSourceQRA (i : Fin 55) :
    QuotientRankAtLeast (spanCodes (plane429GenSourceBasis i)) (plane429GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane429GenBound0000
  | ⟨1, _⟩ => plane429GenBound0001
  | ⟨2, _⟩ => plane429GenBound0002
  | ⟨3, _⟩ => plane429GenBound0003
  | ⟨4, _⟩ => plane429GenBound0004
  | ⟨5, _⟩ => plane429GenBound0005
  | ⟨6, _⟩ => plane429GenBound0006
  | ⟨7, _⟩ => plane429GenBound0007
  | ⟨8, _⟩ => plane429GenBound0008
  | ⟨9, _⟩ => plane429GenBound0009
  | ⟨10, _⟩ => plane429GenBound0010
  | ⟨11, _⟩ => plane429GenBound0011
  | ⟨12, _⟩ => plane429GenBound0012
  | ⟨13, _⟩ => plane429GenBound0013
  | ⟨14, _⟩ => plane429GenBound0014
  | ⟨15, _⟩ => plane429GenBound0015
  | ⟨16, _⟩ => plane429GenBound0016
  | ⟨17, _⟩ => plane429GenBound0017
  | ⟨18, _⟩ => plane429GenBound0018
  | ⟨19, _⟩ => plane429GenBound0019
  | ⟨20, _⟩ => plane429GenBound0020
  | ⟨21, _⟩ => plane429GenBound0021
  | ⟨22, _⟩ => plane429GenBound0022
  | ⟨23, _⟩ => plane429GenBound0023
  | ⟨24, _⟩ => plane429GenBound0024
  | ⟨25, _⟩ => plane429GenBound0025
  | ⟨26, _⟩ => plane429GenBound0026
  | ⟨27, _⟩ => plane429GenBound0027
  | ⟨28, _⟩ => plane429GenBound0028
  | ⟨29, _⟩ => plane429GenBound0029
  | ⟨30, _⟩ => plane429GenBound0030
  | ⟨31, _⟩ => plane429GenBound0031
  | ⟨32, _⟩ => plane429GenBound0032
  | ⟨33, _⟩ => plane429GenBound0033
  | ⟨34, _⟩ => plane429GenBound0034
  | ⟨35, _⟩ => plane429GenBound0035
  | ⟨36, _⟩ => plane429GenBound0036
  | ⟨37, _⟩ => plane429GenBound0037
  | ⟨38, _⟩ => plane429GenBound0038
  | ⟨39, _⟩ => plane429GenBound0039
  | ⟨40, _⟩ => plane429GenBound0040
  | ⟨41, _⟩ => plane429GenBound0041
  | ⟨42, _⟩ => plane429GenBound0042
  | ⟨43, _⟩ => plane429GenBound0043
  | ⟨44, _⟩ => plane429GenBound0044
  | ⟨45, _⟩ => plane429GenBound0045
  | ⟨46, _⟩ => plane429GenBound0046
  | ⟨47, _⟩ => plane429GenBound0047
  | ⟨48, _⟩ => plane429GenBound0048
  | ⟨49, _⟩ => plane429GenBound0049
  | ⟨50, _⟩ => plane429GenBound0050
  | ⟨51, _⟩ => plane429GenBound0051
  | ⟨52, _⟩ => plane429GenBound0052
  | ⟨53, _⟩ => plane429GenBound0053
  | ⟨54, _⟩ => plane429GenBound0054
  | ⟨k + 55, h⟩ => by omega
theorem plane429GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane429GenDeadBasis (0 : Fin 2))) 16 := by
  rw [show plane429GenDeadBasis (0 : Fin 2) = [140, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane429GenSource0000 (by decide)
theorem plane429GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane429GenDeadBasis (1 : Fin 2))) 16 := by
  rw [show plane429GenDeadBasis (1 : Fin 2) = [142, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane429GenSource0001 (by decide)
theorem plane429GenDeadQRA (d : Fin 2) :
    QuotientRankAtLeast (spanCodes (plane429GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane429GenDeadBound0000
  | ⟨1, _⟩ => plane429GenDeadBound0001
  | ⟨k + 2, h⟩ => by omega
end QiushiMatmul
