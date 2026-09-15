import QiushiPlane425GenBindings00
import QiushiPlane425GenBindings01
import QiushiPlane425GenBindings02
import QiushiPlane425GenBindings03
import QiushiPlane425GenBindings04
import QiushiPlane425GenBindings05
import QiushiPlane425GenBindings06
import QiushiPlane425GenBindings07
import QiushiPlane425GenBindings08
import QiushiPlane425GenBindings09
import QiushiPlane425GenBindings10
import QiushiPlane425GenBindings11
import QiushiPlane425GenBindings12
import QiushiPlane425GenBindings13
import QiushiPlane425GenBindings14
import QiushiPlane425GenBindings15
import QiushiPlane425GenBindings16
import QiushiPlane425GenBindings17
import QiushiPlane425GenBindings18
import QiushiPlane425GenBindings19
import QiushiPlane425GenBindings20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane425GenSourceQRA (i : Fin 202) :
    QuotientRankAtLeast (spanCodes (plane425GenSourceBasis i)) (plane425GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane425GenBound0000
  | ⟨1, _⟩ => plane425GenBound0001
  | ⟨2, _⟩ => plane425GenBound0002
  | ⟨3, _⟩ => plane425GenBound0003
  | ⟨4, _⟩ => plane425GenBound0004
  | ⟨5, _⟩ => plane425GenBound0005
  | ⟨6, _⟩ => plane425GenBound0006
  | ⟨7, _⟩ => plane425GenBound0007
  | ⟨8, _⟩ => plane425GenBound0008
  | ⟨9, _⟩ => plane425GenBound0009
  | ⟨10, _⟩ => plane425GenBound0010
  | ⟨11, _⟩ => plane425GenBound0011
  | ⟨12, _⟩ => plane425GenBound0012
  | ⟨13, _⟩ => plane425GenBound0013
  | ⟨14, _⟩ => plane425GenBound0014
  | ⟨15, _⟩ => plane425GenBound0015
  | ⟨16, _⟩ => plane425GenBound0016
  | ⟨17, _⟩ => plane425GenBound0017
  | ⟨18, _⟩ => plane425GenBound0018
  | ⟨19, _⟩ => plane425GenBound0019
  | ⟨20, _⟩ => plane425GenBound0020
  | ⟨21, _⟩ => plane425GenBound0021
  | ⟨22, _⟩ => plane425GenBound0022
  | ⟨23, _⟩ => plane425GenBound0023
  | ⟨24, _⟩ => plane425GenBound0024
  | ⟨25, _⟩ => plane425GenBound0025
  | ⟨26, _⟩ => plane425GenBound0026
  | ⟨27, _⟩ => plane425GenBound0027
  | ⟨28, _⟩ => plane425GenBound0028
  | ⟨29, _⟩ => plane425GenBound0029
  | ⟨30, _⟩ => plane425GenBound0030
  | ⟨31, _⟩ => plane425GenBound0031
  | ⟨32, _⟩ => plane425GenBound0032
  | ⟨33, _⟩ => plane425GenBound0033
  | ⟨34, _⟩ => plane425GenBound0034
  | ⟨35, _⟩ => plane425GenBound0035
  | ⟨36, _⟩ => plane425GenBound0036
  | ⟨37, _⟩ => plane425GenBound0037
  | ⟨38, _⟩ => plane425GenBound0038
  | ⟨39, _⟩ => plane425GenBound0039
  | ⟨40, _⟩ => plane425GenBound0040
  | ⟨41, _⟩ => plane425GenBound0041
  | ⟨42, _⟩ => plane425GenBound0042
  | ⟨43, _⟩ => plane425GenBound0043
  | ⟨44, _⟩ => plane425GenBound0044
  | ⟨45, _⟩ => plane425GenBound0045
  | ⟨46, _⟩ => plane425GenBound0046
  | ⟨47, _⟩ => plane425GenBound0047
  | ⟨48, _⟩ => plane425GenBound0048
  | ⟨49, _⟩ => plane425GenBound0049
  | ⟨50, _⟩ => plane425GenBound0050
  | ⟨51, _⟩ => plane425GenBound0051
  | ⟨52, _⟩ => plane425GenBound0052
  | ⟨53, _⟩ => plane425GenBound0053
  | ⟨54, _⟩ => plane425GenBound0054
  | ⟨55, _⟩ => plane425GenBound0055
  | ⟨56, _⟩ => plane425GenBound0056
  | ⟨57, _⟩ => plane425GenBound0057
  | ⟨58, _⟩ => plane425GenBound0058
  | ⟨59, _⟩ => plane425GenBound0059
  | ⟨60, _⟩ => plane425GenBound0060
  | ⟨61, _⟩ => plane425GenBound0061
  | ⟨62, _⟩ => plane425GenBound0062
  | ⟨63, _⟩ => plane425GenBound0063
  | ⟨64, _⟩ => plane425GenBound0064
  | ⟨65, _⟩ => plane425GenBound0065
  | ⟨66, _⟩ => plane425GenBound0066
  | ⟨67, _⟩ => plane425GenBound0067
  | ⟨68, _⟩ => plane425GenBound0068
  | ⟨69, _⟩ => plane425GenBound0069
  | ⟨70, _⟩ => plane425GenBound0070
  | ⟨71, _⟩ => plane425GenBound0071
  | ⟨72, _⟩ => plane425GenBound0072
  | ⟨73, _⟩ => plane425GenBound0073
  | ⟨74, _⟩ => plane425GenBound0074
  | ⟨75, _⟩ => plane425GenBound0075
  | ⟨76, _⟩ => plane425GenBound0076
  | ⟨77, _⟩ => plane425GenBound0077
  | ⟨78, _⟩ => plane425GenBound0078
  | ⟨79, _⟩ => plane425GenBound0079
  | ⟨80, _⟩ => plane425GenBound0080
  | ⟨81, _⟩ => plane425GenBound0081
  | ⟨82, _⟩ => plane425GenBound0082
  | ⟨83, _⟩ => plane425GenBound0083
  | ⟨84, _⟩ => plane425GenBound0084
  | ⟨85, _⟩ => plane425GenBound0085
  | ⟨86, _⟩ => plane425GenBound0086
  | ⟨87, _⟩ => plane425GenBound0087
  | ⟨88, _⟩ => plane425GenBound0088
  | ⟨89, _⟩ => plane425GenBound0089
  | ⟨90, _⟩ => plane425GenBound0090
  | ⟨91, _⟩ => plane425GenBound0091
  | ⟨92, _⟩ => plane425GenBound0092
  | ⟨93, _⟩ => plane425GenBound0093
  | ⟨94, _⟩ => plane425GenBound0094
  | ⟨95, _⟩ => plane425GenBound0095
  | ⟨96, _⟩ => plane425GenBound0096
  | ⟨97, _⟩ => plane425GenBound0097
  | ⟨98, _⟩ => plane425GenBound0098
  | ⟨99, _⟩ => plane425GenBound0099
  | ⟨100, _⟩ => plane425GenBound0100
  | ⟨101, _⟩ => plane425GenBound0101
  | ⟨102, _⟩ => plane425GenBound0102
  | ⟨103, _⟩ => plane425GenBound0103
  | ⟨104, _⟩ => plane425GenBound0104
  | ⟨105, _⟩ => plane425GenBound0105
  | ⟨106, _⟩ => plane425GenBound0106
  | ⟨107, _⟩ => plane425GenBound0107
  | ⟨108, _⟩ => plane425GenBound0108
  | ⟨109, _⟩ => plane425GenBound0109
  | ⟨110, _⟩ => plane425GenBound0110
  | ⟨111, _⟩ => plane425GenBound0111
  | ⟨112, _⟩ => plane425GenBound0112
  | ⟨113, _⟩ => plane425GenBound0113
  | ⟨114, _⟩ => plane425GenBound0114
  | ⟨115, _⟩ => plane425GenBound0115
  | ⟨116, _⟩ => plane425GenBound0116
  | ⟨117, _⟩ => plane425GenBound0117
  | ⟨118, _⟩ => plane425GenBound0118
  | ⟨119, _⟩ => plane425GenBound0119
  | ⟨120, _⟩ => plane425GenBound0120
  | ⟨121, _⟩ => plane425GenBound0121
  | ⟨122, _⟩ => plane425GenBound0122
  | ⟨123, _⟩ => plane425GenBound0123
  | ⟨124, _⟩ => plane425GenBound0124
  | ⟨125, _⟩ => plane425GenBound0125
  | ⟨126, _⟩ => plane425GenBound0126
  | ⟨127, _⟩ => plane425GenBound0127
  | ⟨128, _⟩ => plane425GenBound0128
  | ⟨129, _⟩ => plane425GenBound0129
  | ⟨130, _⟩ => plane425GenBound0130
  | ⟨131, _⟩ => plane425GenBound0131
  | ⟨132, _⟩ => plane425GenBound0132
  | ⟨133, _⟩ => plane425GenBound0133
  | ⟨134, _⟩ => plane425GenBound0134
  | ⟨135, _⟩ => plane425GenBound0135
  | ⟨136, _⟩ => plane425GenBound0136
  | ⟨137, _⟩ => plane425GenBound0137
  | ⟨138, _⟩ => plane425GenBound0138
  | ⟨139, _⟩ => plane425GenBound0139
  | ⟨140, _⟩ => plane425GenBound0140
  | ⟨141, _⟩ => plane425GenBound0141
  | ⟨142, _⟩ => plane425GenBound0142
  | ⟨143, _⟩ => plane425GenBound0143
  | ⟨144, _⟩ => plane425GenBound0144
  | ⟨145, _⟩ => plane425GenBound0145
  | ⟨146, _⟩ => plane425GenBound0146
  | ⟨147, _⟩ => plane425GenBound0147
  | ⟨148, _⟩ => plane425GenBound0148
  | ⟨149, _⟩ => plane425GenBound0149
  | ⟨150, _⟩ => plane425GenBound0150
  | ⟨151, _⟩ => plane425GenBound0151
  | ⟨152, _⟩ => plane425GenBound0152
  | ⟨153, _⟩ => plane425GenBound0153
  | ⟨154, _⟩ => plane425GenBound0154
  | ⟨155, _⟩ => plane425GenBound0155
  | ⟨156, _⟩ => plane425GenBound0156
  | ⟨157, _⟩ => plane425GenBound0157
  | ⟨158, _⟩ => plane425GenBound0158
  | ⟨159, _⟩ => plane425GenBound0159
  | ⟨160, _⟩ => plane425GenBound0160
  | ⟨161, _⟩ => plane425GenBound0161
  | ⟨162, _⟩ => plane425GenBound0162
  | ⟨163, _⟩ => plane425GenBound0163
  | ⟨164, _⟩ => plane425GenBound0164
  | ⟨165, _⟩ => plane425GenBound0165
  | ⟨166, _⟩ => plane425GenBound0166
  | ⟨167, _⟩ => plane425GenBound0167
  | ⟨168, _⟩ => plane425GenBound0168
  | ⟨169, _⟩ => plane425GenBound0169
  | ⟨170, _⟩ => plane425GenBound0170
  | ⟨171, _⟩ => plane425GenBound0171
  | ⟨172, _⟩ => plane425GenBound0172
  | ⟨173, _⟩ => plane425GenBound0173
  | ⟨174, _⟩ => plane425GenBound0174
  | ⟨175, _⟩ => plane425GenBound0175
  | ⟨176, _⟩ => plane425GenBound0176
  | ⟨177, _⟩ => plane425GenBound0177
  | ⟨178, _⟩ => plane425GenBound0178
  | ⟨179, _⟩ => plane425GenBound0179
  | ⟨180, _⟩ => plane425GenBound0180
  | ⟨181, _⟩ => plane425GenBound0181
  | ⟨182, _⟩ => plane425GenBound0182
  | ⟨183, _⟩ => plane425GenBound0183
  | ⟨184, _⟩ => plane425GenBound0184
  | ⟨185, _⟩ => plane425GenBound0185
  | ⟨186, _⟩ => plane425GenBound0186
  | ⟨187, _⟩ => plane425GenBound0187
  | ⟨188, _⟩ => plane425GenBound0188
  | ⟨189, _⟩ => plane425GenBound0189
  | ⟨190, _⟩ => plane425GenBound0190
  | ⟨191, _⟩ => plane425GenBound0191
  | ⟨192, _⟩ => plane425GenBound0192
  | ⟨193, _⟩ => plane425GenBound0193
  | ⟨194, _⟩ => plane425GenBound0194
  | ⟨195, _⟩ => plane425GenBound0195
  | ⟨196, _⟩ => plane425GenBound0196
  | ⟨197, _⟩ => plane425GenBound0197
  | ⟨198, _⟩ => plane425GenBound0198
  | ⟨199, _⟩ => plane425GenBound0199
  | ⟨200, _⟩ => plane425GenBound0200
  | ⟨201, _⟩ => plane425GenBound0201
  | ⟨k + 202, h⟩ => by omega
theorem plane425GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis (0 : Fin 5))) 17 := by
  rw [show plane425GenDeadBasis (0 : Fin 5) = [258, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane425GenSource0000 (by decide)
theorem plane425GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis (1 : Fin 5))) 17 := by
  rw [show plane425GenDeadBasis (1 : Fin 5) = [258, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane425GenSource0001 (by decide)
theorem plane425GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis (2 : Fin 5))) 17 := by
  rw [show plane425GenDeadBasis (2 : Fin 5) = [258, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane425GenSource0002 (by decide)
theorem plane425GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis (3 : Fin 5))) 17 := by
  rw [show plane425GenDeadBasis (3 : Fin 5) = [258, 64, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane425GenSource0003 (by decide)
theorem plane425GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis (4 : Fin 5))) 17 := by
  rw [show plane425GenDeadBasis (4 : Fin 5) = [258, 70, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane425GenSource0004 (by decide)
theorem plane425GenDeadQRA (d : Fin 5) :
    QuotientRankAtLeast (spanCodes (plane425GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane425GenDeadBound0000
  | ⟨1, _⟩ => plane425GenDeadBound0001
  | ⟨2, _⟩ => plane425GenDeadBound0002
  | ⟨3, _⟩ => plane425GenDeadBound0003
  | ⟨4, _⟩ => plane425GenDeadBound0004
  | ⟨k + 5, h⟩ => by omega
end QiushiMatmul
