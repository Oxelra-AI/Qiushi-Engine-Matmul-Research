import QiushiPlane473GenBindings00
import QiushiPlane473GenBindings01
import QiushiPlane473GenBindings02
import QiushiPlane473GenBindings03
import QiushiPlane473GenBindings04
import QiushiPlane473GenBindings05
import QiushiPlane473GenBindings06
import QiushiPlane473GenBindings07
import QiushiPlane473GenBindings08
import QiushiPlane473GenBindings09
import QiushiPlane473GenBindings10
import QiushiPlane473GenBindings11
import QiushiPlane473GenBindings12
import QiushiPlane473GenBindings13
import QiushiPlane473GenBindings14
import QiushiPlane473GenBindings15
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane473GenSourceQRA (i : Fin 153) :
    QuotientRankAtLeast (spanCodes (plane473GenSourceBasis i)) (plane473GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane473GenBound0000
  | ⟨1, _⟩ => plane473GenBound0001
  | ⟨2, _⟩ => plane473GenBound0002
  | ⟨3, _⟩ => plane473GenBound0003
  | ⟨4, _⟩ => plane473GenBound0004
  | ⟨5, _⟩ => plane473GenBound0005
  | ⟨6, _⟩ => plane473GenBound0006
  | ⟨7, _⟩ => plane473GenBound0007
  | ⟨8, _⟩ => plane473GenBound0008
  | ⟨9, _⟩ => plane473GenBound0009
  | ⟨10, _⟩ => plane473GenBound0010
  | ⟨11, _⟩ => plane473GenBound0011
  | ⟨12, _⟩ => plane473GenBound0012
  | ⟨13, _⟩ => plane473GenBound0013
  | ⟨14, _⟩ => plane473GenBound0014
  | ⟨15, _⟩ => plane473GenBound0015
  | ⟨16, _⟩ => plane473GenBound0016
  | ⟨17, _⟩ => plane473GenBound0017
  | ⟨18, _⟩ => plane473GenBound0018
  | ⟨19, _⟩ => plane473GenBound0019
  | ⟨20, _⟩ => plane473GenBound0020
  | ⟨21, _⟩ => plane473GenBound0021
  | ⟨22, _⟩ => plane473GenBound0022
  | ⟨23, _⟩ => plane473GenBound0023
  | ⟨24, _⟩ => plane473GenBound0024
  | ⟨25, _⟩ => plane473GenBound0025
  | ⟨26, _⟩ => plane473GenBound0026
  | ⟨27, _⟩ => plane473GenBound0027
  | ⟨28, _⟩ => plane473GenBound0028
  | ⟨29, _⟩ => plane473GenBound0029
  | ⟨30, _⟩ => plane473GenBound0030
  | ⟨31, _⟩ => plane473GenBound0031
  | ⟨32, _⟩ => plane473GenBound0032
  | ⟨33, _⟩ => plane473GenBound0033
  | ⟨34, _⟩ => plane473GenBound0034
  | ⟨35, _⟩ => plane473GenBound0035
  | ⟨36, _⟩ => plane473GenBound0036
  | ⟨37, _⟩ => plane473GenBound0037
  | ⟨38, _⟩ => plane473GenBound0038
  | ⟨39, _⟩ => plane473GenBound0039
  | ⟨40, _⟩ => plane473GenBound0040
  | ⟨41, _⟩ => plane473GenBound0041
  | ⟨42, _⟩ => plane473GenBound0042
  | ⟨43, _⟩ => plane473GenBound0043
  | ⟨44, _⟩ => plane473GenBound0044
  | ⟨45, _⟩ => plane473GenBound0045
  | ⟨46, _⟩ => plane473GenBound0046
  | ⟨47, _⟩ => plane473GenBound0047
  | ⟨48, _⟩ => plane473GenBound0048
  | ⟨49, _⟩ => plane473GenBound0049
  | ⟨50, _⟩ => plane473GenBound0050
  | ⟨51, _⟩ => plane473GenBound0051
  | ⟨52, _⟩ => plane473GenBound0052
  | ⟨53, _⟩ => plane473GenBound0053
  | ⟨54, _⟩ => plane473GenBound0054
  | ⟨55, _⟩ => plane473GenBound0055
  | ⟨56, _⟩ => plane473GenBound0056
  | ⟨57, _⟩ => plane473GenBound0057
  | ⟨58, _⟩ => plane473GenBound0058
  | ⟨59, _⟩ => plane473GenBound0059
  | ⟨60, _⟩ => plane473GenBound0060
  | ⟨61, _⟩ => plane473GenBound0061
  | ⟨62, _⟩ => plane473GenBound0062
  | ⟨63, _⟩ => plane473GenBound0063
  | ⟨64, _⟩ => plane473GenBound0064
  | ⟨65, _⟩ => plane473GenBound0065
  | ⟨66, _⟩ => plane473GenBound0066
  | ⟨67, _⟩ => plane473GenBound0067
  | ⟨68, _⟩ => plane473GenBound0068
  | ⟨69, _⟩ => plane473GenBound0069
  | ⟨70, _⟩ => plane473GenBound0070
  | ⟨71, _⟩ => plane473GenBound0071
  | ⟨72, _⟩ => plane473GenBound0072
  | ⟨73, _⟩ => plane473GenBound0073
  | ⟨74, _⟩ => plane473GenBound0074
  | ⟨75, _⟩ => plane473GenBound0075
  | ⟨76, _⟩ => plane473GenBound0076
  | ⟨77, _⟩ => plane473GenBound0077
  | ⟨78, _⟩ => plane473GenBound0078
  | ⟨79, _⟩ => plane473GenBound0079
  | ⟨80, _⟩ => plane473GenBound0080
  | ⟨81, _⟩ => plane473GenBound0081
  | ⟨82, _⟩ => plane473GenBound0082
  | ⟨83, _⟩ => plane473GenBound0083
  | ⟨84, _⟩ => plane473GenBound0084
  | ⟨85, _⟩ => plane473GenBound0085
  | ⟨86, _⟩ => plane473GenBound0086
  | ⟨87, _⟩ => plane473GenBound0087
  | ⟨88, _⟩ => plane473GenBound0088
  | ⟨89, _⟩ => plane473GenBound0089
  | ⟨90, _⟩ => plane473GenBound0090
  | ⟨91, _⟩ => plane473GenBound0091
  | ⟨92, _⟩ => plane473GenBound0092
  | ⟨93, _⟩ => plane473GenBound0093
  | ⟨94, _⟩ => plane473GenBound0094
  | ⟨95, _⟩ => plane473GenBound0095
  | ⟨96, _⟩ => plane473GenBound0096
  | ⟨97, _⟩ => plane473GenBound0097
  | ⟨98, _⟩ => plane473GenBound0098
  | ⟨99, _⟩ => plane473GenBound0099
  | ⟨100, _⟩ => plane473GenBound0100
  | ⟨101, _⟩ => plane473GenBound0101
  | ⟨102, _⟩ => plane473GenBound0102
  | ⟨103, _⟩ => plane473GenBound0103
  | ⟨104, _⟩ => plane473GenBound0104
  | ⟨105, _⟩ => plane473GenBound0105
  | ⟨106, _⟩ => plane473GenBound0106
  | ⟨107, _⟩ => plane473GenBound0107
  | ⟨108, _⟩ => plane473GenBound0108
  | ⟨109, _⟩ => plane473GenBound0109
  | ⟨110, _⟩ => plane473GenBound0110
  | ⟨111, _⟩ => plane473GenBound0111
  | ⟨112, _⟩ => plane473GenBound0112
  | ⟨113, _⟩ => plane473GenBound0113
  | ⟨114, _⟩ => plane473GenBound0114
  | ⟨115, _⟩ => plane473GenBound0115
  | ⟨116, _⟩ => plane473GenBound0116
  | ⟨117, _⟩ => plane473GenBound0117
  | ⟨118, _⟩ => plane473GenBound0118
  | ⟨119, _⟩ => plane473GenBound0119
  | ⟨120, _⟩ => plane473GenBound0120
  | ⟨121, _⟩ => plane473GenBound0121
  | ⟨122, _⟩ => plane473GenBound0122
  | ⟨123, _⟩ => plane473GenBound0123
  | ⟨124, _⟩ => plane473GenBound0124
  | ⟨125, _⟩ => plane473GenBound0125
  | ⟨126, _⟩ => plane473GenBound0126
  | ⟨127, _⟩ => plane473GenBound0127
  | ⟨128, _⟩ => plane473GenBound0128
  | ⟨129, _⟩ => plane473GenBound0129
  | ⟨130, _⟩ => plane473GenBound0130
  | ⟨131, _⟩ => plane473GenBound0131
  | ⟨132, _⟩ => plane473GenBound0132
  | ⟨133, _⟩ => plane473GenBound0133
  | ⟨134, _⟩ => plane473GenBound0134
  | ⟨135, _⟩ => plane473GenBound0135
  | ⟨136, _⟩ => plane473GenBound0136
  | ⟨137, _⟩ => plane473GenBound0137
  | ⟨138, _⟩ => plane473GenBound0138
  | ⟨139, _⟩ => plane473GenBound0139
  | ⟨140, _⟩ => plane473GenBound0140
  | ⟨141, _⟩ => plane473GenBound0141
  | ⟨142, _⟩ => plane473GenBound0142
  | ⟨143, _⟩ => plane473GenBound0143
  | ⟨144, _⟩ => plane473GenBound0144
  | ⟨145, _⟩ => plane473GenBound0145
  | ⟨146, _⟩ => plane473GenBound0146
  | ⟨147, _⟩ => plane473GenBound0147
  | ⟨148, _⟩ => plane473GenBound0148
  | ⟨149, _⟩ => plane473GenBound0149
  | ⟨150, _⟩ => plane473GenBound0150
  | ⟨151, _⟩ => plane473GenBound0151
  | ⟨152, _⟩ => plane473GenBound0152
  | ⟨k + 153, h⟩ => by omega
theorem plane473GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane473GenDeadBasis (0 : Fin 4))) 17 := by
  rw [show plane473GenDeadBasis (0 : Fin 4) = [293, 68, 16, 10] from rfl]
  exact quotientRankAtLeast_weaken plane473GenSource0000 (by decide)
theorem plane473GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane473GenDeadBasis (1 : Fin 4))) 17 := by
  rw [show plane473GenDeadBasis (1 : Fin 4) = [293, 69, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane473GenSource0001 (by decide)
theorem plane473GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane473GenDeadBasis (2 : Fin 4))) 17 := by
  rw [show plane473GenDeadBasis (2 : Fin 4) = [293, 165, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane473GenSource0002 (by decide)
theorem plane473GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane473GenDeadBasis (3 : Fin 4))) 17 := by
  rw [show plane473GenDeadBasis (3 : Fin 4) = [293, 182, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane473GenSource0003 (by decide)
theorem plane473GenDeadQRA (d : Fin 4) :
    QuotientRankAtLeast (spanCodes (plane473GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane473GenDeadBound0000
  | ⟨1, _⟩ => plane473GenDeadBound0001
  | ⟨2, _⟩ => plane473GenDeadBound0002
  | ⟨3, _⟩ => plane473GenDeadBound0003
  | ⟨k + 4, h⟩ => by omega
end QiushiMatmul
