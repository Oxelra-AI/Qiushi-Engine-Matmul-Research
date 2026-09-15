import QiushiPlane467GenBindings00
import QiushiPlane467GenBindings01
import QiushiPlane467GenBindings02
import QiushiPlane467GenBindings03
import QiushiPlane467GenBindings04
import QiushiPlane467GenBindings05
import QiushiPlane467GenBindings06
import QiushiPlane467GenBindings07
import QiushiPlane467GenBindings08
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane467GenSourceQRA (i : Fin 84) :
    QuotientRankAtLeast (spanCodes (plane467GenSourceBasis i)) (plane467GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane467GenBound0000
  | ⟨1, _⟩ => plane467GenBound0001
  | ⟨2, _⟩ => plane467GenBound0002
  | ⟨3, _⟩ => plane467GenBound0003
  | ⟨4, _⟩ => plane467GenBound0004
  | ⟨5, _⟩ => plane467GenBound0005
  | ⟨6, _⟩ => plane467GenBound0006
  | ⟨7, _⟩ => plane467GenBound0007
  | ⟨8, _⟩ => plane467GenBound0008
  | ⟨9, _⟩ => plane467GenBound0009
  | ⟨10, _⟩ => plane467GenBound0010
  | ⟨11, _⟩ => plane467GenBound0011
  | ⟨12, _⟩ => plane467GenBound0012
  | ⟨13, _⟩ => plane467GenBound0013
  | ⟨14, _⟩ => plane467GenBound0014
  | ⟨15, _⟩ => plane467GenBound0015
  | ⟨16, _⟩ => plane467GenBound0016
  | ⟨17, _⟩ => plane467GenBound0017
  | ⟨18, _⟩ => plane467GenBound0018
  | ⟨19, _⟩ => plane467GenBound0019
  | ⟨20, _⟩ => plane467GenBound0020
  | ⟨21, _⟩ => plane467GenBound0021
  | ⟨22, _⟩ => plane467GenBound0022
  | ⟨23, _⟩ => plane467GenBound0023
  | ⟨24, _⟩ => plane467GenBound0024
  | ⟨25, _⟩ => plane467GenBound0025
  | ⟨26, _⟩ => plane467GenBound0026
  | ⟨27, _⟩ => plane467GenBound0027
  | ⟨28, _⟩ => plane467GenBound0028
  | ⟨29, _⟩ => plane467GenBound0029
  | ⟨30, _⟩ => plane467GenBound0030
  | ⟨31, _⟩ => plane467GenBound0031
  | ⟨32, _⟩ => plane467GenBound0032
  | ⟨33, _⟩ => plane467GenBound0033
  | ⟨34, _⟩ => plane467GenBound0034
  | ⟨35, _⟩ => plane467GenBound0035
  | ⟨36, _⟩ => plane467GenBound0036
  | ⟨37, _⟩ => plane467GenBound0037
  | ⟨38, _⟩ => plane467GenBound0038
  | ⟨39, _⟩ => plane467GenBound0039
  | ⟨40, _⟩ => plane467GenBound0040
  | ⟨41, _⟩ => plane467GenBound0041
  | ⟨42, _⟩ => plane467GenBound0042
  | ⟨43, _⟩ => plane467GenBound0043
  | ⟨44, _⟩ => plane467GenBound0044
  | ⟨45, _⟩ => plane467GenBound0045
  | ⟨46, _⟩ => plane467GenBound0046
  | ⟨47, _⟩ => plane467GenBound0047
  | ⟨48, _⟩ => plane467GenBound0048
  | ⟨49, _⟩ => plane467GenBound0049
  | ⟨50, _⟩ => plane467GenBound0050
  | ⟨51, _⟩ => plane467GenBound0051
  | ⟨52, _⟩ => plane467GenBound0052
  | ⟨53, _⟩ => plane467GenBound0053
  | ⟨54, _⟩ => plane467GenBound0054
  | ⟨55, _⟩ => plane467GenBound0055
  | ⟨56, _⟩ => plane467GenBound0056
  | ⟨57, _⟩ => plane467GenBound0057
  | ⟨58, _⟩ => plane467GenBound0058
  | ⟨59, _⟩ => plane467GenBound0059
  | ⟨60, _⟩ => plane467GenBound0060
  | ⟨61, _⟩ => plane467GenBound0061
  | ⟨62, _⟩ => plane467GenBound0062
  | ⟨63, _⟩ => plane467GenBound0063
  | ⟨64, _⟩ => plane467GenBound0064
  | ⟨65, _⟩ => plane467GenBound0065
  | ⟨66, _⟩ => plane467GenBound0066
  | ⟨67, _⟩ => plane467GenBound0067
  | ⟨68, _⟩ => plane467GenBound0068
  | ⟨69, _⟩ => plane467GenBound0069
  | ⟨70, _⟩ => plane467GenBound0070
  | ⟨71, _⟩ => plane467GenBound0071
  | ⟨72, _⟩ => plane467GenBound0072
  | ⟨73, _⟩ => plane467GenBound0073
  | ⟨74, _⟩ => plane467GenBound0074
  | ⟨75, _⟩ => plane467GenBound0075
  | ⟨76, _⟩ => plane467GenBound0076
  | ⟨77, _⟩ => plane467GenBound0077
  | ⟨78, _⟩ => plane467GenBound0078
  | ⟨79, _⟩ => plane467GenBound0079
  | ⟨80, _⟩ => plane467GenBound0080
  | ⟨81, _⟩ => plane467GenBound0081
  | ⟨82, _⟩ => plane467GenBound0082
  | ⟨83, _⟩ => plane467GenBound0083
  | ⟨k + 84, h⟩ => by omega
theorem plane467GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane467GenDeadBasis (0 : Fin 4))) 17 := by
  rw [show plane467GenDeadBasis (0 : Fin 4) = [260, 163, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane467GenSource0000 (by decide)
theorem plane467GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane467GenDeadBasis (1 : Fin 4))) 17 := by
  rw [show plane467GenDeadBasis (1 : Fin 4) = [261, 163, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane467GenSource0001 (by decide)
theorem plane467GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane467GenDeadBasis (2 : Fin 4))) 17 := by
  rw [show plane467GenDeadBasis (2 : Fin 4) = [276, 163, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane467GenSource0002 (by decide)
theorem plane467GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane467GenDeadBasis (3 : Fin 4))) 17 := by
  rw [show plane467GenDeadBasis (3 : Fin 4) = [277, 163, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane467GenSource0003 (by decide)
theorem plane467GenDeadQRA (d : Fin 4) :
    QuotientRankAtLeast (spanCodes (plane467GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane467GenDeadBound0000
  | ⟨1, _⟩ => plane467GenDeadBound0001
  | ⟨2, _⟩ => plane467GenDeadBound0002
  | ⟨3, _⟩ => plane467GenDeadBound0003
  | ⟨k + 4, h⟩ => by omega
end QiushiMatmul
