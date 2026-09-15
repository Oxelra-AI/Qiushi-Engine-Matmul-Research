import QiushiPlane458GenBindings00
import QiushiPlane458GenBindings01
import QiushiPlane458GenBindings02
import QiushiPlane458GenBindings03
import QiushiPlane458GenBindings04
import QiushiPlane458GenBindings05
import QiushiPlane458GenBindings06
import QiushiPlane458GenBindings07
import QiushiPlane458GenBindings08
import QiushiPlane458GenBindings09
import QiushiPlane458GenBindings10
import QiushiPlane458GenBindings11
import QiushiPlane458GenBindings12
import QiushiPlane458GenBindings13
import QiushiPlane458GenBindings14
import QiushiPlane458GenBindings15
import QiushiPlane458GenBindings16
import QiushiPlane458GenBindings17
import QiushiPlane458GenBindings18
import QiushiPlane458GenBindings19
import QiushiPlane458GenBindings20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane458GenSourceQRA (i : Fin 203) :
    QuotientRankAtLeast (spanCodes (plane458GenSourceBasis i)) (plane458GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane458GenBound0000
  | ⟨1, _⟩ => plane458GenBound0001
  | ⟨2, _⟩ => plane458GenBound0002
  | ⟨3, _⟩ => plane458GenBound0003
  | ⟨4, _⟩ => plane458GenBound0004
  | ⟨5, _⟩ => plane458GenBound0005
  | ⟨6, _⟩ => plane458GenBound0006
  | ⟨7, _⟩ => plane458GenBound0007
  | ⟨8, _⟩ => plane458GenBound0008
  | ⟨9, _⟩ => plane458GenBound0009
  | ⟨10, _⟩ => plane458GenBound0010
  | ⟨11, _⟩ => plane458GenBound0011
  | ⟨12, _⟩ => plane458GenBound0012
  | ⟨13, _⟩ => plane458GenBound0013
  | ⟨14, _⟩ => plane458GenBound0014
  | ⟨15, _⟩ => plane458GenBound0015
  | ⟨16, _⟩ => plane458GenBound0016
  | ⟨17, _⟩ => plane458GenBound0017
  | ⟨18, _⟩ => plane458GenBound0018
  | ⟨19, _⟩ => plane458GenBound0019
  | ⟨20, _⟩ => plane458GenBound0020
  | ⟨21, _⟩ => plane458GenBound0021
  | ⟨22, _⟩ => plane458GenBound0022
  | ⟨23, _⟩ => plane458GenBound0023
  | ⟨24, _⟩ => plane458GenBound0024
  | ⟨25, _⟩ => plane458GenBound0025
  | ⟨26, _⟩ => plane458GenBound0026
  | ⟨27, _⟩ => plane458GenBound0027
  | ⟨28, _⟩ => plane458GenBound0028
  | ⟨29, _⟩ => plane458GenBound0029
  | ⟨30, _⟩ => plane458GenBound0030
  | ⟨31, _⟩ => plane458GenBound0031
  | ⟨32, _⟩ => plane458GenBound0032
  | ⟨33, _⟩ => plane458GenBound0033
  | ⟨34, _⟩ => plane458GenBound0034
  | ⟨35, _⟩ => plane458GenBound0035
  | ⟨36, _⟩ => plane458GenBound0036
  | ⟨37, _⟩ => plane458GenBound0037
  | ⟨38, _⟩ => plane458GenBound0038
  | ⟨39, _⟩ => plane458GenBound0039
  | ⟨40, _⟩ => plane458GenBound0040
  | ⟨41, _⟩ => plane458GenBound0041
  | ⟨42, _⟩ => plane458GenBound0042
  | ⟨43, _⟩ => plane458GenBound0043
  | ⟨44, _⟩ => plane458GenBound0044
  | ⟨45, _⟩ => plane458GenBound0045
  | ⟨46, _⟩ => plane458GenBound0046
  | ⟨47, _⟩ => plane458GenBound0047
  | ⟨48, _⟩ => plane458GenBound0048
  | ⟨49, _⟩ => plane458GenBound0049
  | ⟨50, _⟩ => plane458GenBound0050
  | ⟨51, _⟩ => plane458GenBound0051
  | ⟨52, _⟩ => plane458GenBound0052
  | ⟨53, _⟩ => plane458GenBound0053
  | ⟨54, _⟩ => plane458GenBound0054
  | ⟨55, _⟩ => plane458GenBound0055
  | ⟨56, _⟩ => plane458GenBound0056
  | ⟨57, _⟩ => plane458GenBound0057
  | ⟨58, _⟩ => plane458GenBound0058
  | ⟨59, _⟩ => plane458GenBound0059
  | ⟨60, _⟩ => plane458GenBound0060
  | ⟨61, _⟩ => plane458GenBound0061
  | ⟨62, _⟩ => plane458GenBound0062
  | ⟨63, _⟩ => plane458GenBound0063
  | ⟨64, _⟩ => plane458GenBound0064
  | ⟨65, _⟩ => plane458GenBound0065
  | ⟨66, _⟩ => plane458GenBound0066
  | ⟨67, _⟩ => plane458GenBound0067
  | ⟨68, _⟩ => plane458GenBound0068
  | ⟨69, _⟩ => plane458GenBound0069
  | ⟨70, _⟩ => plane458GenBound0070
  | ⟨71, _⟩ => plane458GenBound0071
  | ⟨72, _⟩ => plane458GenBound0072
  | ⟨73, _⟩ => plane458GenBound0073
  | ⟨74, _⟩ => plane458GenBound0074
  | ⟨75, _⟩ => plane458GenBound0075
  | ⟨76, _⟩ => plane458GenBound0076
  | ⟨77, _⟩ => plane458GenBound0077
  | ⟨78, _⟩ => plane458GenBound0078
  | ⟨79, _⟩ => plane458GenBound0079
  | ⟨80, _⟩ => plane458GenBound0080
  | ⟨81, _⟩ => plane458GenBound0081
  | ⟨82, _⟩ => plane458GenBound0082
  | ⟨83, _⟩ => plane458GenBound0083
  | ⟨84, _⟩ => plane458GenBound0084
  | ⟨85, _⟩ => plane458GenBound0085
  | ⟨86, _⟩ => plane458GenBound0086
  | ⟨87, _⟩ => plane458GenBound0087
  | ⟨88, _⟩ => plane458GenBound0088
  | ⟨89, _⟩ => plane458GenBound0089
  | ⟨90, _⟩ => plane458GenBound0090
  | ⟨91, _⟩ => plane458GenBound0091
  | ⟨92, _⟩ => plane458GenBound0092
  | ⟨93, _⟩ => plane458GenBound0093
  | ⟨94, _⟩ => plane458GenBound0094
  | ⟨95, _⟩ => plane458GenBound0095
  | ⟨96, _⟩ => plane458GenBound0096
  | ⟨97, _⟩ => plane458GenBound0097
  | ⟨98, _⟩ => plane458GenBound0098
  | ⟨99, _⟩ => plane458GenBound0099
  | ⟨100, _⟩ => plane458GenBound0100
  | ⟨101, _⟩ => plane458GenBound0101
  | ⟨102, _⟩ => plane458GenBound0102
  | ⟨103, _⟩ => plane458GenBound0103
  | ⟨104, _⟩ => plane458GenBound0104
  | ⟨105, _⟩ => plane458GenBound0105
  | ⟨106, _⟩ => plane458GenBound0106
  | ⟨107, _⟩ => plane458GenBound0107
  | ⟨108, _⟩ => plane458GenBound0108
  | ⟨109, _⟩ => plane458GenBound0109
  | ⟨110, _⟩ => plane458GenBound0110
  | ⟨111, _⟩ => plane458GenBound0111
  | ⟨112, _⟩ => plane458GenBound0112
  | ⟨113, _⟩ => plane458GenBound0113
  | ⟨114, _⟩ => plane458GenBound0114
  | ⟨115, _⟩ => plane458GenBound0115
  | ⟨116, _⟩ => plane458GenBound0116
  | ⟨117, _⟩ => plane458GenBound0117
  | ⟨118, _⟩ => plane458GenBound0118
  | ⟨119, _⟩ => plane458GenBound0119
  | ⟨120, _⟩ => plane458GenBound0120
  | ⟨121, _⟩ => plane458GenBound0121
  | ⟨122, _⟩ => plane458GenBound0122
  | ⟨123, _⟩ => plane458GenBound0123
  | ⟨124, _⟩ => plane458GenBound0124
  | ⟨125, _⟩ => plane458GenBound0125
  | ⟨126, _⟩ => plane458GenBound0126
  | ⟨127, _⟩ => plane458GenBound0127
  | ⟨128, _⟩ => plane458GenBound0128
  | ⟨129, _⟩ => plane458GenBound0129
  | ⟨130, _⟩ => plane458GenBound0130
  | ⟨131, _⟩ => plane458GenBound0131
  | ⟨132, _⟩ => plane458GenBound0132
  | ⟨133, _⟩ => plane458GenBound0133
  | ⟨134, _⟩ => plane458GenBound0134
  | ⟨135, _⟩ => plane458GenBound0135
  | ⟨136, _⟩ => plane458GenBound0136
  | ⟨137, _⟩ => plane458GenBound0137
  | ⟨138, _⟩ => plane458GenBound0138
  | ⟨139, _⟩ => plane458GenBound0139
  | ⟨140, _⟩ => plane458GenBound0140
  | ⟨141, _⟩ => plane458GenBound0141
  | ⟨142, _⟩ => plane458GenBound0142
  | ⟨143, _⟩ => plane458GenBound0143
  | ⟨144, _⟩ => plane458GenBound0144
  | ⟨145, _⟩ => plane458GenBound0145
  | ⟨146, _⟩ => plane458GenBound0146
  | ⟨147, _⟩ => plane458GenBound0147
  | ⟨148, _⟩ => plane458GenBound0148
  | ⟨149, _⟩ => plane458GenBound0149
  | ⟨150, _⟩ => plane458GenBound0150
  | ⟨151, _⟩ => plane458GenBound0151
  | ⟨152, _⟩ => plane458GenBound0152
  | ⟨153, _⟩ => plane458GenBound0153
  | ⟨154, _⟩ => plane458GenBound0154
  | ⟨155, _⟩ => plane458GenBound0155
  | ⟨156, _⟩ => plane458GenBound0156
  | ⟨157, _⟩ => plane458GenBound0157
  | ⟨158, _⟩ => plane458GenBound0158
  | ⟨159, _⟩ => plane458GenBound0159
  | ⟨160, _⟩ => plane458GenBound0160
  | ⟨161, _⟩ => plane458GenBound0161
  | ⟨162, _⟩ => plane458GenBound0162
  | ⟨163, _⟩ => plane458GenBound0163
  | ⟨164, _⟩ => plane458GenBound0164
  | ⟨165, _⟩ => plane458GenBound0165
  | ⟨166, _⟩ => plane458GenBound0166
  | ⟨167, _⟩ => plane458GenBound0167
  | ⟨168, _⟩ => plane458GenBound0168
  | ⟨169, _⟩ => plane458GenBound0169
  | ⟨170, _⟩ => plane458GenBound0170
  | ⟨171, _⟩ => plane458GenBound0171
  | ⟨172, _⟩ => plane458GenBound0172
  | ⟨173, _⟩ => plane458GenBound0173
  | ⟨174, _⟩ => plane458GenBound0174
  | ⟨175, _⟩ => plane458GenBound0175
  | ⟨176, _⟩ => plane458GenBound0176
  | ⟨177, _⟩ => plane458GenBound0177
  | ⟨178, _⟩ => plane458GenBound0178
  | ⟨179, _⟩ => plane458GenBound0179
  | ⟨180, _⟩ => plane458GenBound0180
  | ⟨181, _⟩ => plane458GenBound0181
  | ⟨182, _⟩ => plane458GenBound0182
  | ⟨183, _⟩ => plane458GenBound0183
  | ⟨184, _⟩ => plane458GenBound0184
  | ⟨185, _⟩ => plane458GenBound0185
  | ⟨186, _⟩ => plane458GenBound0186
  | ⟨187, _⟩ => plane458GenBound0187
  | ⟨188, _⟩ => plane458GenBound0188
  | ⟨189, _⟩ => plane458GenBound0189
  | ⟨190, _⟩ => plane458GenBound0190
  | ⟨191, _⟩ => plane458GenBound0191
  | ⟨192, _⟩ => plane458GenBound0192
  | ⟨193, _⟩ => plane458GenBound0193
  | ⟨194, _⟩ => plane458GenBound0194
  | ⟨195, _⟩ => plane458GenBound0195
  | ⟨196, _⟩ => plane458GenBound0196
  | ⟨197, _⟩ => plane458GenBound0197
  | ⟨198, _⟩ => plane458GenBound0198
  | ⟨199, _⟩ => plane458GenBound0199
  | ⟨200, _⟩ => plane458GenBound0200
  | ⟨201, _⟩ => plane458GenBound0201
  | ⟨202, _⟩ => plane458GenBound0202
  | ⟨k + 203, h⟩ => by omega
theorem plane458GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (0 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (0 : Fin 7) = [450, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0000 (by decide)
theorem plane458GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (1 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (1 : Fin 7) = [389, 71, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0001 (by decide)
theorem plane458GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (2 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (2 : Fin 7) = [416, 98, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0002 (by decide)
theorem plane458GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (3 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (3 : Fin 7) = [321, 131, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0003 (by decide)
theorem plane458GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (4 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (4 : Fin 7) = [356, 166, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0004 (by decide)
theorem plane458GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (5 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (5 : Fin 7) = [262, 196, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0005 (by decide)
theorem plane458GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis (6 : Fin 7))) 17 := by
  rw [show plane458GenDeadBasis (6 : Fin 7) = [291, 225, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane458GenSource0006 (by decide)
theorem plane458GenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane458GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane458GenDeadBound0000
  | ⟨1, _⟩ => plane458GenDeadBound0001
  | ⟨2, _⟩ => plane458GenDeadBound0002
  | ⟨3, _⟩ => plane458GenDeadBound0003
  | ⟨4, _⟩ => plane458GenDeadBound0004
  | ⟨5, _⟩ => plane458GenDeadBound0005
  | ⟨6, _⟩ => plane458GenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
