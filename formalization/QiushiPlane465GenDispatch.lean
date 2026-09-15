import QiushiPlane465GenBindings00
import QiushiPlane465GenBindings01
import QiushiPlane465GenBindings02
import QiushiPlane465GenBindings03
import QiushiPlane465GenBindings04
import QiushiPlane465GenBindings05
import QiushiPlane465GenBindings06
import QiushiPlane465GenBindings07
import QiushiPlane465GenBindings08
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane465GenSourceQRA (i : Fin 88) :
    QuotientRankAtLeast (spanCodes (plane465GenSourceBasis i)) (plane465GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane465GenBound0000
  | ⟨1, _⟩ => plane465GenBound0001
  | ⟨2, _⟩ => plane465GenBound0002
  | ⟨3, _⟩ => plane465GenBound0003
  | ⟨4, _⟩ => plane465GenBound0004
  | ⟨5, _⟩ => plane465GenBound0005
  | ⟨6, _⟩ => plane465GenBound0006
  | ⟨7, _⟩ => plane465GenBound0007
  | ⟨8, _⟩ => plane465GenBound0008
  | ⟨9, _⟩ => plane465GenBound0009
  | ⟨10, _⟩ => plane465GenBound0010
  | ⟨11, _⟩ => plane465GenBound0011
  | ⟨12, _⟩ => plane465GenBound0012
  | ⟨13, _⟩ => plane465GenBound0013
  | ⟨14, _⟩ => plane465GenBound0014
  | ⟨15, _⟩ => plane465GenBound0015
  | ⟨16, _⟩ => plane465GenBound0016
  | ⟨17, _⟩ => plane465GenBound0017
  | ⟨18, _⟩ => plane465GenBound0018
  | ⟨19, _⟩ => plane465GenBound0019
  | ⟨20, _⟩ => plane465GenBound0020
  | ⟨21, _⟩ => plane465GenBound0021
  | ⟨22, _⟩ => plane465GenBound0022
  | ⟨23, _⟩ => plane465GenBound0023
  | ⟨24, _⟩ => plane465GenBound0024
  | ⟨25, _⟩ => plane465GenBound0025
  | ⟨26, _⟩ => plane465GenBound0026
  | ⟨27, _⟩ => plane465GenBound0027
  | ⟨28, _⟩ => plane465GenBound0028
  | ⟨29, _⟩ => plane465GenBound0029
  | ⟨30, _⟩ => plane465GenBound0030
  | ⟨31, _⟩ => plane465GenBound0031
  | ⟨32, _⟩ => plane465GenBound0032
  | ⟨33, _⟩ => plane465GenBound0033
  | ⟨34, _⟩ => plane465GenBound0034
  | ⟨35, _⟩ => plane465GenBound0035
  | ⟨36, _⟩ => plane465GenBound0036
  | ⟨37, _⟩ => plane465GenBound0037
  | ⟨38, _⟩ => plane465GenBound0038
  | ⟨39, _⟩ => plane465GenBound0039
  | ⟨40, _⟩ => plane465GenBound0040
  | ⟨41, _⟩ => plane465GenBound0041
  | ⟨42, _⟩ => plane465GenBound0042
  | ⟨43, _⟩ => plane465GenBound0043
  | ⟨44, _⟩ => plane465GenBound0044
  | ⟨45, _⟩ => plane465GenBound0045
  | ⟨46, _⟩ => plane465GenBound0046
  | ⟨47, _⟩ => plane465GenBound0047
  | ⟨48, _⟩ => plane465GenBound0048
  | ⟨49, _⟩ => plane465GenBound0049
  | ⟨50, _⟩ => plane465GenBound0050
  | ⟨51, _⟩ => plane465GenBound0051
  | ⟨52, _⟩ => plane465GenBound0052
  | ⟨53, _⟩ => plane465GenBound0053
  | ⟨54, _⟩ => plane465GenBound0054
  | ⟨55, _⟩ => plane465GenBound0055
  | ⟨56, _⟩ => plane465GenBound0056
  | ⟨57, _⟩ => plane465GenBound0057
  | ⟨58, _⟩ => plane465GenBound0058
  | ⟨59, _⟩ => plane465GenBound0059
  | ⟨60, _⟩ => plane465GenBound0060
  | ⟨61, _⟩ => plane465GenBound0061
  | ⟨62, _⟩ => plane465GenBound0062
  | ⟨63, _⟩ => plane465GenBound0063
  | ⟨64, _⟩ => plane465GenBound0064
  | ⟨65, _⟩ => plane465GenBound0065
  | ⟨66, _⟩ => plane465GenBound0066
  | ⟨67, _⟩ => plane465GenBound0067
  | ⟨68, _⟩ => plane465GenBound0068
  | ⟨69, _⟩ => plane465GenBound0069
  | ⟨70, _⟩ => plane465GenBound0070
  | ⟨71, _⟩ => plane465GenBound0071
  | ⟨72, _⟩ => plane465GenBound0072
  | ⟨73, _⟩ => plane465GenBound0073
  | ⟨74, _⟩ => plane465GenBound0074
  | ⟨75, _⟩ => plane465GenBound0075
  | ⟨76, _⟩ => plane465GenBound0076
  | ⟨77, _⟩ => plane465GenBound0077
  | ⟨78, _⟩ => plane465GenBound0078
  | ⟨79, _⟩ => plane465GenBound0079
  | ⟨80, _⟩ => plane465GenBound0080
  | ⟨81, _⟩ => plane465GenBound0081
  | ⟨82, _⟩ => plane465GenBound0082
  | ⟨83, _⟩ => plane465GenBound0083
  | ⟨84, _⟩ => plane465GenBound0084
  | ⟨85, _⟩ => plane465GenBound0085
  | ⟨86, _⟩ => plane465GenBound0086
  | ⟨87, _⟩ => plane465GenBound0087
  | ⟨k + 88, h⟩ => by omega
theorem plane465GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (0 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (0 : Fin 6) = [289, 68, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0000 (by decide)
theorem plane465GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (1 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (1 : Fin 6) = [291, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0001 (by decide)
theorem plane465GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (2 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (2 : Fin 6) = [257, 68, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0002 (by decide)
theorem plane465GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (3 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (3 : Fin 6) = [261, 68, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0003 (by decide)
theorem plane465GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (4 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (4 : Fin 6) = [304, 129, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0004 (by decide)
theorem plane465GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis (5 : Fin 6))) 17 := by
  rw [show plane465GenDeadBasis (5 : Fin 6) = [304, 135, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane465GenSource0005 (by decide)
theorem plane465GenDeadQRA (d : Fin 6) :
    QuotientRankAtLeast (spanCodes (plane465GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane465GenDeadBound0000
  | ⟨1, _⟩ => plane465GenDeadBound0001
  | ⟨2, _⟩ => plane465GenDeadBound0002
  | ⟨3, _⟩ => plane465GenDeadBound0003
  | ⟨4, _⟩ => plane465GenDeadBound0004
  | ⟨5, _⟩ => plane465GenDeadBound0005
  | ⟨k + 6, h⟩ => by omega
end QiushiMatmul
