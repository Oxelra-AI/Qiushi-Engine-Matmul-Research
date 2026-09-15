import QiushiPlane461GenBindings00
import QiushiPlane461GenBindings01
import QiushiPlane461GenBindings02
import QiushiPlane461GenBindings03
import QiushiPlane461GenBindings04
import QiushiPlane461GenBindings05
import QiushiPlane461GenBindings06
import QiushiPlane461GenBindings07
import QiushiPlane461GenBindings08
import QiushiPlane461GenBindings09
import QiushiPlane461GenBindings10
import QiushiPlane461GenBindings11
import QiushiPlane461GenBindings12
import QiushiPlane461GenBindings13
import QiushiPlane461GenBindings14
import QiushiPlane461GenBindings15
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane461GenSourceQRA (i : Fin 151) :
    QuotientRankAtLeast (spanCodes (plane461GenSourceBasis i)) (plane461GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane461GenBound0000
  | ⟨1, _⟩ => plane461GenBound0001
  | ⟨2, _⟩ => plane461GenBound0002
  | ⟨3, _⟩ => plane461GenBound0003
  | ⟨4, _⟩ => plane461GenBound0004
  | ⟨5, _⟩ => plane461GenBound0005
  | ⟨6, _⟩ => plane461GenBound0006
  | ⟨7, _⟩ => plane461GenBound0007
  | ⟨8, _⟩ => plane461GenBound0008
  | ⟨9, _⟩ => plane461GenBound0009
  | ⟨10, _⟩ => plane461GenBound0010
  | ⟨11, _⟩ => plane461GenBound0011
  | ⟨12, _⟩ => plane461GenBound0012
  | ⟨13, _⟩ => plane461GenBound0013
  | ⟨14, _⟩ => plane461GenBound0014
  | ⟨15, _⟩ => plane461GenBound0015
  | ⟨16, _⟩ => plane461GenBound0016
  | ⟨17, _⟩ => plane461GenBound0017
  | ⟨18, _⟩ => plane461GenBound0018
  | ⟨19, _⟩ => plane461GenBound0019
  | ⟨20, _⟩ => plane461GenBound0020
  | ⟨21, _⟩ => plane461GenBound0021
  | ⟨22, _⟩ => plane461GenBound0022
  | ⟨23, _⟩ => plane461GenBound0023
  | ⟨24, _⟩ => plane461GenBound0024
  | ⟨25, _⟩ => plane461GenBound0025
  | ⟨26, _⟩ => plane461GenBound0026
  | ⟨27, _⟩ => plane461GenBound0027
  | ⟨28, _⟩ => plane461GenBound0028
  | ⟨29, _⟩ => plane461GenBound0029
  | ⟨30, _⟩ => plane461GenBound0030
  | ⟨31, _⟩ => plane461GenBound0031
  | ⟨32, _⟩ => plane461GenBound0032
  | ⟨33, _⟩ => plane461GenBound0033
  | ⟨34, _⟩ => plane461GenBound0034
  | ⟨35, _⟩ => plane461GenBound0035
  | ⟨36, _⟩ => plane461GenBound0036
  | ⟨37, _⟩ => plane461GenBound0037
  | ⟨38, _⟩ => plane461GenBound0038
  | ⟨39, _⟩ => plane461GenBound0039
  | ⟨40, _⟩ => plane461GenBound0040
  | ⟨41, _⟩ => plane461GenBound0041
  | ⟨42, _⟩ => plane461GenBound0042
  | ⟨43, _⟩ => plane461GenBound0043
  | ⟨44, _⟩ => plane461GenBound0044
  | ⟨45, _⟩ => plane461GenBound0045
  | ⟨46, _⟩ => plane461GenBound0046
  | ⟨47, _⟩ => plane461GenBound0047
  | ⟨48, _⟩ => plane461GenBound0048
  | ⟨49, _⟩ => plane461GenBound0049
  | ⟨50, _⟩ => plane461GenBound0050
  | ⟨51, _⟩ => plane461GenBound0051
  | ⟨52, _⟩ => plane461GenBound0052
  | ⟨53, _⟩ => plane461GenBound0053
  | ⟨54, _⟩ => plane461GenBound0054
  | ⟨55, _⟩ => plane461GenBound0055
  | ⟨56, _⟩ => plane461GenBound0056
  | ⟨57, _⟩ => plane461GenBound0057
  | ⟨58, _⟩ => plane461GenBound0058
  | ⟨59, _⟩ => plane461GenBound0059
  | ⟨60, _⟩ => plane461GenBound0060
  | ⟨61, _⟩ => plane461GenBound0061
  | ⟨62, _⟩ => plane461GenBound0062
  | ⟨63, _⟩ => plane461GenBound0063
  | ⟨64, _⟩ => plane461GenBound0064
  | ⟨65, _⟩ => plane461GenBound0065
  | ⟨66, _⟩ => plane461GenBound0066
  | ⟨67, _⟩ => plane461GenBound0067
  | ⟨68, _⟩ => plane461GenBound0068
  | ⟨69, _⟩ => plane461GenBound0069
  | ⟨70, _⟩ => plane461GenBound0070
  | ⟨71, _⟩ => plane461GenBound0071
  | ⟨72, _⟩ => plane461GenBound0072
  | ⟨73, _⟩ => plane461GenBound0073
  | ⟨74, _⟩ => plane461GenBound0074
  | ⟨75, _⟩ => plane461GenBound0075
  | ⟨76, _⟩ => plane461GenBound0076
  | ⟨77, _⟩ => plane461GenBound0077
  | ⟨78, _⟩ => plane461GenBound0078
  | ⟨79, _⟩ => plane461GenBound0079
  | ⟨80, _⟩ => plane461GenBound0080
  | ⟨81, _⟩ => plane461GenBound0081
  | ⟨82, _⟩ => plane461GenBound0082
  | ⟨83, _⟩ => plane461GenBound0083
  | ⟨84, _⟩ => plane461GenBound0084
  | ⟨85, _⟩ => plane461GenBound0085
  | ⟨86, _⟩ => plane461GenBound0086
  | ⟨87, _⟩ => plane461GenBound0087
  | ⟨88, _⟩ => plane461GenBound0088
  | ⟨89, _⟩ => plane461GenBound0089
  | ⟨90, _⟩ => plane461GenBound0090
  | ⟨91, _⟩ => plane461GenBound0091
  | ⟨92, _⟩ => plane461GenBound0092
  | ⟨93, _⟩ => plane461GenBound0093
  | ⟨94, _⟩ => plane461GenBound0094
  | ⟨95, _⟩ => plane461GenBound0095
  | ⟨96, _⟩ => plane461GenBound0096
  | ⟨97, _⟩ => plane461GenBound0097
  | ⟨98, _⟩ => plane461GenBound0098
  | ⟨99, _⟩ => plane461GenBound0099
  | ⟨100, _⟩ => plane461GenBound0100
  | ⟨101, _⟩ => plane461GenBound0101
  | ⟨102, _⟩ => plane461GenBound0102
  | ⟨103, _⟩ => plane461GenBound0103
  | ⟨104, _⟩ => plane461GenBound0104
  | ⟨105, _⟩ => plane461GenBound0105
  | ⟨106, _⟩ => plane461GenBound0106
  | ⟨107, _⟩ => plane461GenBound0107
  | ⟨108, _⟩ => plane461GenBound0108
  | ⟨109, _⟩ => plane461GenBound0109
  | ⟨110, _⟩ => plane461GenBound0110
  | ⟨111, _⟩ => plane461GenBound0111
  | ⟨112, _⟩ => plane461GenBound0112
  | ⟨113, _⟩ => plane461GenBound0113
  | ⟨114, _⟩ => plane461GenBound0114
  | ⟨115, _⟩ => plane461GenBound0115
  | ⟨116, _⟩ => plane461GenBound0116
  | ⟨117, _⟩ => plane461GenBound0117
  | ⟨118, _⟩ => plane461GenBound0118
  | ⟨119, _⟩ => plane461GenBound0119
  | ⟨120, _⟩ => plane461GenBound0120
  | ⟨121, _⟩ => plane461GenBound0121
  | ⟨122, _⟩ => plane461GenBound0122
  | ⟨123, _⟩ => plane461GenBound0123
  | ⟨124, _⟩ => plane461GenBound0124
  | ⟨125, _⟩ => plane461GenBound0125
  | ⟨126, _⟩ => plane461GenBound0126
  | ⟨127, _⟩ => plane461GenBound0127
  | ⟨128, _⟩ => plane461GenBound0128
  | ⟨129, _⟩ => plane461GenBound0129
  | ⟨130, _⟩ => plane461GenBound0130
  | ⟨131, _⟩ => plane461GenBound0131
  | ⟨132, _⟩ => plane461GenBound0132
  | ⟨133, _⟩ => plane461GenBound0133
  | ⟨134, _⟩ => plane461GenBound0134
  | ⟨135, _⟩ => plane461GenBound0135
  | ⟨136, _⟩ => plane461GenBound0136
  | ⟨137, _⟩ => plane461GenBound0137
  | ⟨138, _⟩ => plane461GenBound0138
  | ⟨139, _⟩ => plane461GenBound0139
  | ⟨140, _⟩ => plane461GenBound0140
  | ⟨141, _⟩ => plane461GenBound0141
  | ⟨142, _⟩ => plane461GenBound0142
  | ⟨143, _⟩ => plane461GenBound0143
  | ⟨144, _⟩ => plane461GenBound0144
  | ⟨145, _⟩ => plane461GenBound0145
  | ⟨146, _⟩ => plane461GenBound0146
  | ⟨147, _⟩ => plane461GenBound0147
  | ⟨148, _⟩ => plane461GenBound0148
  | ⟨149, _⟩ => plane461GenBound0149
  | ⟨150, _⟩ => plane461GenBound0150
  | ⟨k + 151, h⟩ => by omega
theorem plane461GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane461GenDeadBasis (0 : Fin 1))) 17 := by
  rw [show plane461GenDeadBasis (0 : Fin 1) = [162, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane461GenSource0000 (by decide)
theorem plane461GenDeadQRA (d : Fin 1) :
    QuotientRankAtLeast (spanCodes (plane461GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane461GenDeadBound0000
  | ⟨k + 1, h⟩ => by omega
end QiushiMatmul
