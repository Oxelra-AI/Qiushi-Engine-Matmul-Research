import QiushiPlane475GenBindings00
import QiushiPlane475GenBindings01
import QiushiPlane475GenBindings02
import QiushiPlane475GenBindings03
import QiushiPlane475GenBindings04
import QiushiPlane475GenBindings05
import QiushiPlane475GenBindings06
import QiushiPlane475GenBindings07
import QiushiPlane475GenBindings08
import QiushiPlane475GenBindings09
import QiushiPlane475GenBindings10
import QiushiPlane475GenBindings11
import QiushiPlane475GenBindings12
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane475GenSourceQRA (i : Fin 126) :
    QuotientRankAtLeast (spanCodes (plane475GenSourceBasis i)) (plane475GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane475GenBound0000
  | ⟨1, _⟩ => plane475GenBound0001
  | ⟨2, _⟩ => plane475GenBound0002
  | ⟨3, _⟩ => plane475GenBound0003
  | ⟨4, _⟩ => plane475GenBound0004
  | ⟨5, _⟩ => plane475GenBound0005
  | ⟨6, _⟩ => plane475GenBound0006
  | ⟨7, _⟩ => plane475GenBound0007
  | ⟨8, _⟩ => plane475GenBound0008
  | ⟨9, _⟩ => plane475GenBound0009
  | ⟨10, _⟩ => plane475GenBound0010
  | ⟨11, _⟩ => plane475GenBound0011
  | ⟨12, _⟩ => plane475GenBound0012
  | ⟨13, _⟩ => plane475GenBound0013
  | ⟨14, _⟩ => plane475GenBound0014
  | ⟨15, _⟩ => plane475GenBound0015
  | ⟨16, _⟩ => plane475GenBound0016
  | ⟨17, _⟩ => plane475GenBound0017
  | ⟨18, _⟩ => plane475GenBound0018
  | ⟨19, _⟩ => plane475GenBound0019
  | ⟨20, _⟩ => plane475GenBound0020
  | ⟨21, _⟩ => plane475GenBound0021
  | ⟨22, _⟩ => plane475GenBound0022
  | ⟨23, _⟩ => plane475GenBound0023
  | ⟨24, _⟩ => plane475GenBound0024
  | ⟨25, _⟩ => plane475GenBound0025
  | ⟨26, _⟩ => plane475GenBound0026
  | ⟨27, _⟩ => plane475GenBound0027
  | ⟨28, _⟩ => plane475GenBound0028
  | ⟨29, _⟩ => plane475GenBound0029
  | ⟨30, _⟩ => plane475GenBound0030
  | ⟨31, _⟩ => plane475GenBound0031
  | ⟨32, _⟩ => plane475GenBound0032
  | ⟨33, _⟩ => plane475GenBound0033
  | ⟨34, _⟩ => plane475GenBound0034
  | ⟨35, _⟩ => plane475GenBound0035
  | ⟨36, _⟩ => plane475GenBound0036
  | ⟨37, _⟩ => plane475GenBound0037
  | ⟨38, _⟩ => plane475GenBound0038
  | ⟨39, _⟩ => plane475GenBound0039
  | ⟨40, _⟩ => plane475GenBound0040
  | ⟨41, _⟩ => plane475GenBound0041
  | ⟨42, _⟩ => plane475GenBound0042
  | ⟨43, _⟩ => plane475GenBound0043
  | ⟨44, _⟩ => plane475GenBound0044
  | ⟨45, _⟩ => plane475GenBound0045
  | ⟨46, _⟩ => plane475GenBound0046
  | ⟨47, _⟩ => plane475GenBound0047
  | ⟨48, _⟩ => plane475GenBound0048
  | ⟨49, _⟩ => plane475GenBound0049
  | ⟨50, _⟩ => plane475GenBound0050
  | ⟨51, _⟩ => plane475GenBound0051
  | ⟨52, _⟩ => plane475GenBound0052
  | ⟨53, _⟩ => plane475GenBound0053
  | ⟨54, _⟩ => plane475GenBound0054
  | ⟨55, _⟩ => plane475GenBound0055
  | ⟨56, _⟩ => plane475GenBound0056
  | ⟨57, _⟩ => plane475GenBound0057
  | ⟨58, _⟩ => plane475GenBound0058
  | ⟨59, _⟩ => plane475GenBound0059
  | ⟨60, _⟩ => plane475GenBound0060
  | ⟨61, _⟩ => plane475GenBound0061
  | ⟨62, _⟩ => plane475GenBound0062
  | ⟨63, _⟩ => plane475GenBound0063
  | ⟨64, _⟩ => plane475GenBound0064
  | ⟨65, _⟩ => plane475GenBound0065
  | ⟨66, _⟩ => plane475GenBound0066
  | ⟨67, _⟩ => plane475GenBound0067
  | ⟨68, _⟩ => plane475GenBound0068
  | ⟨69, _⟩ => plane475GenBound0069
  | ⟨70, _⟩ => plane475GenBound0070
  | ⟨71, _⟩ => plane475GenBound0071
  | ⟨72, _⟩ => plane475GenBound0072
  | ⟨73, _⟩ => plane475GenBound0073
  | ⟨74, _⟩ => plane475GenBound0074
  | ⟨75, _⟩ => plane475GenBound0075
  | ⟨76, _⟩ => plane475GenBound0076
  | ⟨77, _⟩ => plane475GenBound0077
  | ⟨78, _⟩ => plane475GenBound0078
  | ⟨79, _⟩ => plane475GenBound0079
  | ⟨80, _⟩ => plane475GenBound0080
  | ⟨81, _⟩ => plane475GenBound0081
  | ⟨82, _⟩ => plane475GenBound0082
  | ⟨83, _⟩ => plane475GenBound0083
  | ⟨84, _⟩ => plane475GenBound0084
  | ⟨85, _⟩ => plane475GenBound0085
  | ⟨86, _⟩ => plane475GenBound0086
  | ⟨87, _⟩ => plane475GenBound0087
  | ⟨88, _⟩ => plane475GenBound0088
  | ⟨89, _⟩ => plane475GenBound0089
  | ⟨90, _⟩ => plane475GenBound0090
  | ⟨91, _⟩ => plane475GenBound0091
  | ⟨92, _⟩ => plane475GenBound0092
  | ⟨93, _⟩ => plane475GenBound0093
  | ⟨94, _⟩ => plane475GenBound0094
  | ⟨95, _⟩ => plane475GenBound0095
  | ⟨96, _⟩ => plane475GenBound0096
  | ⟨97, _⟩ => plane475GenBound0097
  | ⟨98, _⟩ => plane475GenBound0098
  | ⟨99, _⟩ => plane475GenBound0099
  | ⟨100, _⟩ => plane475GenBound0100
  | ⟨101, _⟩ => plane475GenBound0101
  | ⟨102, _⟩ => plane475GenBound0102
  | ⟨103, _⟩ => plane475GenBound0103
  | ⟨104, _⟩ => plane475GenBound0104
  | ⟨105, _⟩ => plane475GenBound0105
  | ⟨106, _⟩ => plane475GenBound0106
  | ⟨107, _⟩ => plane475GenBound0107
  | ⟨108, _⟩ => plane475GenBound0108
  | ⟨109, _⟩ => plane475GenBound0109
  | ⟨110, _⟩ => plane475GenBound0110
  | ⟨111, _⟩ => plane475GenBound0111
  | ⟨112, _⟩ => plane475GenBound0112
  | ⟨113, _⟩ => plane475GenBound0113
  | ⟨114, _⟩ => plane475GenBound0114
  | ⟨115, _⟩ => plane475GenBound0115
  | ⟨116, _⟩ => plane475GenBound0116
  | ⟨117, _⟩ => plane475GenBound0117
  | ⟨118, _⟩ => plane475GenBound0118
  | ⟨119, _⟩ => plane475GenBound0119
  | ⟨120, _⟩ => plane475GenBound0120
  | ⟨121, _⟩ => plane475GenBound0121
  | ⟨122, _⟩ => plane475GenBound0122
  | ⟨123, _⟩ => plane475GenBound0123
  | ⟨124, _⟩ => plane475GenBound0124
  | ⟨125, _⟩ => plane475GenBound0125
  | ⟨k + 126, h⟩ => by omega
theorem plane475GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (0 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (0 : Fin 7) = [165, 96, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0000 (by decide)
theorem plane475GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (1 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (1 : Fin 7) = [131, 70, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0001 (by decide)
theorem plane475GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (2 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (2 : Fin 7) = [150, 83, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0002 (by decide)
theorem plane475GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (3 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (3 : Fin 7) = [257, 165, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0003 (by decide)
theorem plane475GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (4 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (4 : Fin 7) = [276, 165, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0004 (by decide)
theorem plane475GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (5 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (5 : Fin 7) = [295, 165, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0005 (by decide)
theorem plane475GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis (6 : Fin 7))) 17 := by
  rw [show plane475GenDeadBasis (6 : Fin 7) = [306, 165, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane475GenSource0006 (by decide)
theorem plane475GenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane475GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane475GenDeadBound0000
  | ⟨1, _⟩ => plane475GenDeadBound0001
  | ⟨2, _⟩ => plane475GenDeadBound0002
  | ⟨3, _⟩ => plane475GenDeadBound0003
  | ⟨4, _⟩ => plane475GenDeadBound0004
  | ⟨5, _⟩ => plane475GenDeadBound0005
  | ⟨6, _⟩ => plane475GenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
