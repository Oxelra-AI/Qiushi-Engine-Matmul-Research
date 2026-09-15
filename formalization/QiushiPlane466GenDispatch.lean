import QiushiPlane466GenBindings00
import QiushiPlane466GenBindings01
import QiushiPlane466GenBindings02
import QiushiPlane466GenBindings03
import QiushiPlane466GenBindings04
import QiushiPlane466GenBindings05
import QiushiPlane466GenBindings06
import QiushiPlane466GenBindings07
import QiushiPlane466GenBindings08
import QiushiPlane466GenBindings09
import QiushiPlane466GenBindings10
import QiushiPlane466GenBindings11
import QiushiPlane466GenBindings12
import QiushiPlane466GenBindings13
import QiushiPlane466GenBindings14
import QiushiPlane466GenBindings15
import QiushiPlane466GenBindings16
import QiushiPlane466GenBindings17
import QiushiPlane466GenBindings18
import QiushiPlane466GenBindings19
import QiushiPlane466GenBindings20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane466GenSourceQRA (i : Fin 210) :
    QuotientRankAtLeast (spanCodes (plane466GenSourceBasis i)) (plane466GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane466GenBound0000
  | ⟨1, _⟩ => plane466GenBound0001
  | ⟨2, _⟩ => plane466GenBound0002
  | ⟨3, _⟩ => plane466GenBound0003
  | ⟨4, _⟩ => plane466GenBound0004
  | ⟨5, _⟩ => plane466GenBound0005
  | ⟨6, _⟩ => plane466GenBound0006
  | ⟨7, _⟩ => plane466GenBound0007
  | ⟨8, _⟩ => plane466GenBound0008
  | ⟨9, _⟩ => plane466GenBound0009
  | ⟨10, _⟩ => plane466GenBound0010
  | ⟨11, _⟩ => plane466GenBound0011
  | ⟨12, _⟩ => plane466GenBound0012
  | ⟨13, _⟩ => plane466GenBound0013
  | ⟨14, _⟩ => plane466GenBound0014
  | ⟨15, _⟩ => plane466GenBound0015
  | ⟨16, _⟩ => plane466GenBound0016
  | ⟨17, _⟩ => plane466GenBound0017
  | ⟨18, _⟩ => plane466GenBound0018
  | ⟨19, _⟩ => plane466GenBound0019
  | ⟨20, _⟩ => plane466GenBound0020
  | ⟨21, _⟩ => plane466GenBound0021
  | ⟨22, _⟩ => plane466GenBound0022
  | ⟨23, _⟩ => plane466GenBound0023
  | ⟨24, _⟩ => plane466GenBound0024
  | ⟨25, _⟩ => plane466GenBound0025
  | ⟨26, _⟩ => plane466GenBound0026
  | ⟨27, _⟩ => plane466GenBound0027
  | ⟨28, _⟩ => plane466GenBound0028
  | ⟨29, _⟩ => plane466GenBound0029
  | ⟨30, _⟩ => plane466GenBound0030
  | ⟨31, _⟩ => plane466GenBound0031
  | ⟨32, _⟩ => plane466GenBound0032
  | ⟨33, _⟩ => plane466GenBound0033
  | ⟨34, _⟩ => plane466GenBound0034
  | ⟨35, _⟩ => plane466GenBound0035
  | ⟨36, _⟩ => plane466GenBound0036
  | ⟨37, _⟩ => plane466GenBound0037
  | ⟨38, _⟩ => plane466GenBound0038
  | ⟨39, _⟩ => plane466GenBound0039
  | ⟨40, _⟩ => plane466GenBound0040
  | ⟨41, _⟩ => plane466GenBound0041
  | ⟨42, _⟩ => plane466GenBound0042
  | ⟨43, _⟩ => plane466GenBound0043
  | ⟨44, _⟩ => plane466GenBound0044
  | ⟨45, _⟩ => plane466GenBound0045
  | ⟨46, _⟩ => plane466GenBound0046
  | ⟨47, _⟩ => plane466GenBound0047
  | ⟨48, _⟩ => plane466GenBound0048
  | ⟨49, _⟩ => plane466GenBound0049
  | ⟨50, _⟩ => plane466GenBound0050
  | ⟨51, _⟩ => plane466GenBound0051
  | ⟨52, _⟩ => plane466GenBound0052
  | ⟨53, _⟩ => plane466GenBound0053
  | ⟨54, _⟩ => plane466GenBound0054
  | ⟨55, _⟩ => plane466GenBound0055
  | ⟨56, _⟩ => plane466GenBound0056
  | ⟨57, _⟩ => plane466GenBound0057
  | ⟨58, _⟩ => plane466GenBound0058
  | ⟨59, _⟩ => plane466GenBound0059
  | ⟨60, _⟩ => plane466GenBound0060
  | ⟨61, _⟩ => plane466GenBound0061
  | ⟨62, _⟩ => plane466GenBound0062
  | ⟨63, _⟩ => plane466GenBound0063
  | ⟨64, _⟩ => plane466GenBound0064
  | ⟨65, _⟩ => plane466GenBound0065
  | ⟨66, _⟩ => plane466GenBound0066
  | ⟨67, _⟩ => plane466GenBound0067
  | ⟨68, _⟩ => plane466GenBound0068
  | ⟨69, _⟩ => plane466GenBound0069
  | ⟨70, _⟩ => plane466GenBound0070
  | ⟨71, _⟩ => plane466GenBound0071
  | ⟨72, _⟩ => plane466GenBound0072
  | ⟨73, _⟩ => plane466GenBound0073
  | ⟨74, _⟩ => plane466GenBound0074
  | ⟨75, _⟩ => plane466GenBound0075
  | ⟨76, _⟩ => plane466GenBound0076
  | ⟨77, _⟩ => plane466GenBound0077
  | ⟨78, _⟩ => plane466GenBound0078
  | ⟨79, _⟩ => plane466GenBound0079
  | ⟨80, _⟩ => plane466GenBound0080
  | ⟨81, _⟩ => plane466GenBound0081
  | ⟨82, _⟩ => plane466GenBound0082
  | ⟨83, _⟩ => plane466GenBound0083
  | ⟨84, _⟩ => plane466GenBound0084
  | ⟨85, _⟩ => plane466GenBound0085
  | ⟨86, _⟩ => plane466GenBound0086
  | ⟨87, _⟩ => plane466GenBound0087
  | ⟨88, _⟩ => plane466GenBound0088
  | ⟨89, _⟩ => plane466GenBound0089
  | ⟨90, _⟩ => plane466GenBound0090
  | ⟨91, _⟩ => plane466GenBound0091
  | ⟨92, _⟩ => plane466GenBound0092
  | ⟨93, _⟩ => plane466GenBound0093
  | ⟨94, _⟩ => plane466GenBound0094
  | ⟨95, _⟩ => plane466GenBound0095
  | ⟨96, _⟩ => plane466GenBound0096
  | ⟨97, _⟩ => plane466GenBound0097
  | ⟨98, _⟩ => plane466GenBound0098
  | ⟨99, _⟩ => plane466GenBound0099
  | ⟨100, _⟩ => plane466GenBound0100
  | ⟨101, _⟩ => plane466GenBound0101
  | ⟨102, _⟩ => plane466GenBound0102
  | ⟨103, _⟩ => plane466GenBound0103
  | ⟨104, _⟩ => plane466GenBound0104
  | ⟨105, _⟩ => plane466GenBound0105
  | ⟨106, _⟩ => plane466GenBound0106
  | ⟨107, _⟩ => plane466GenBound0107
  | ⟨108, _⟩ => plane466GenBound0108
  | ⟨109, _⟩ => plane466GenBound0109
  | ⟨110, _⟩ => plane466GenBound0110
  | ⟨111, _⟩ => plane466GenBound0111
  | ⟨112, _⟩ => plane466GenBound0112
  | ⟨113, _⟩ => plane466GenBound0113
  | ⟨114, _⟩ => plane466GenBound0114
  | ⟨115, _⟩ => plane466GenBound0115
  | ⟨116, _⟩ => plane466GenBound0116
  | ⟨117, _⟩ => plane466GenBound0117
  | ⟨118, _⟩ => plane466GenBound0118
  | ⟨119, _⟩ => plane466GenBound0119
  | ⟨120, _⟩ => plane466GenBound0120
  | ⟨121, _⟩ => plane466GenBound0121
  | ⟨122, _⟩ => plane466GenBound0122
  | ⟨123, _⟩ => plane466GenBound0123
  | ⟨124, _⟩ => plane466GenBound0124
  | ⟨125, _⟩ => plane466GenBound0125
  | ⟨126, _⟩ => plane466GenBound0126
  | ⟨127, _⟩ => plane466GenBound0127
  | ⟨128, _⟩ => plane466GenBound0128
  | ⟨129, _⟩ => plane466GenBound0129
  | ⟨130, _⟩ => plane466GenBound0130
  | ⟨131, _⟩ => plane466GenBound0131
  | ⟨132, _⟩ => plane466GenBound0132
  | ⟨133, _⟩ => plane466GenBound0133
  | ⟨134, _⟩ => plane466GenBound0134
  | ⟨135, _⟩ => plane466GenBound0135
  | ⟨136, _⟩ => plane466GenBound0136
  | ⟨137, _⟩ => plane466GenBound0137
  | ⟨138, _⟩ => plane466GenBound0138
  | ⟨139, _⟩ => plane466GenBound0139
  | ⟨140, _⟩ => plane466GenBound0140
  | ⟨141, _⟩ => plane466GenBound0141
  | ⟨142, _⟩ => plane466GenBound0142
  | ⟨143, _⟩ => plane466GenBound0143
  | ⟨144, _⟩ => plane466GenBound0144
  | ⟨145, _⟩ => plane466GenBound0145
  | ⟨146, _⟩ => plane466GenBound0146
  | ⟨147, _⟩ => plane466GenBound0147
  | ⟨148, _⟩ => plane466GenBound0148
  | ⟨149, _⟩ => plane466GenBound0149
  | ⟨150, _⟩ => plane466GenBound0150
  | ⟨151, _⟩ => plane466GenBound0151
  | ⟨152, _⟩ => plane466GenBound0152
  | ⟨153, _⟩ => plane466GenBound0153
  | ⟨154, _⟩ => plane466GenBound0154
  | ⟨155, _⟩ => plane466GenBound0155
  | ⟨156, _⟩ => plane466GenBound0156
  | ⟨157, _⟩ => plane466GenBound0157
  | ⟨158, _⟩ => plane466GenBound0158
  | ⟨159, _⟩ => plane466GenBound0159
  | ⟨160, _⟩ => plane466GenBound0160
  | ⟨161, _⟩ => plane466GenBound0161
  | ⟨162, _⟩ => plane466GenBound0162
  | ⟨163, _⟩ => plane466GenBound0163
  | ⟨164, _⟩ => plane466GenBound0164
  | ⟨165, _⟩ => plane466GenBound0165
  | ⟨166, _⟩ => plane466GenBound0166
  | ⟨167, _⟩ => plane466GenBound0167
  | ⟨168, _⟩ => plane466GenBound0168
  | ⟨169, _⟩ => plane466GenBound0169
  | ⟨170, _⟩ => plane466GenBound0170
  | ⟨171, _⟩ => plane466GenBound0171
  | ⟨172, _⟩ => plane466GenBound0172
  | ⟨173, _⟩ => plane466GenBound0173
  | ⟨174, _⟩ => plane466GenBound0174
  | ⟨175, _⟩ => plane466GenBound0175
  | ⟨176, _⟩ => plane466GenBound0176
  | ⟨177, _⟩ => plane466GenBound0177
  | ⟨178, _⟩ => plane466GenBound0178
  | ⟨179, _⟩ => plane466GenBound0179
  | ⟨180, _⟩ => plane466GenBound0180
  | ⟨181, _⟩ => plane466GenBound0181
  | ⟨182, _⟩ => plane466GenBound0182
  | ⟨183, _⟩ => plane466GenBound0183
  | ⟨184, _⟩ => plane466GenBound0184
  | ⟨185, _⟩ => plane466GenBound0185
  | ⟨186, _⟩ => plane466GenBound0186
  | ⟨187, _⟩ => plane466GenBound0187
  | ⟨188, _⟩ => plane466GenBound0188
  | ⟨189, _⟩ => plane466GenBound0189
  | ⟨190, _⟩ => plane466GenBound0190
  | ⟨191, _⟩ => plane466GenBound0191
  | ⟨192, _⟩ => plane466GenBound0192
  | ⟨193, _⟩ => plane466GenBound0193
  | ⟨194, _⟩ => plane466GenBound0194
  | ⟨195, _⟩ => plane466GenBound0195
  | ⟨196, _⟩ => plane466GenBound0196
  | ⟨197, _⟩ => plane466GenBound0197
  | ⟨198, _⟩ => plane466GenBound0198
  | ⟨199, _⟩ => plane466GenBound0199
  | ⟨200, _⟩ => plane466GenBound0200
  | ⟨201, _⟩ => plane466GenBound0201
  | ⟨202, _⟩ => plane466GenBound0202
  | ⟨203, _⟩ => plane466GenBound0203
  | ⟨204, _⟩ => plane466GenBound0204
  | ⟨205, _⟩ => plane466GenBound0205
  | ⟨206, _⟩ => plane466GenBound0206
  | ⟨207, _⟩ => plane466GenBound0207
  | ⟨208, _⟩ => plane466GenBound0208
  | ⟨209, _⟩ => plane466GenBound0209
  | ⟨k + 210, h⟩ => by omega
theorem plane466GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (0 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (0 : Fin 13) = [293, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0000 (by decide)
theorem plane466GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (1 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (1 : Fin 13) = [295, 68, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0001 (by decide)
theorem plane466GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (2 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (2 : Fin 13) = [274, 68, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0002 (by decide)
theorem plane466GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (3 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (3 : Fin 13) = [276, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0003 (by decide)
theorem plane466GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (4 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (4 : Fin 13) = [258, 68, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0004 (by decide)
theorem plane466GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (5 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (5 : Fin 13) = [262, 68, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0005 (by decide)
theorem plane466GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (6 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (6 : Fin 13) = [305, 131, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0006 (by decide)
theorem plane466GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (7 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (7 : Fin 13) = [305, 133, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0007 (by decide)
theorem plane466GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (8 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (8 : Fin 13) = [305, 147, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0008 (by decide)
theorem plane466GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (9 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (9 : Fin 13) = [305, 151, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0009 (by decide)
theorem plane466GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (10 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (10 : Fin 13) = [305, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0010 (by decide)
theorem plane466GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (11 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (11 : Fin 13) = [305, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0011 (by decide)
theorem plane466GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis (12 : Fin 13))) 17 := by
  rw [show plane466GenDeadBasis (12 : Fin 13) = [305, 182, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane466GenSource0012 (by decide)
theorem plane466GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane466GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane466GenDeadBound0000
  | ⟨1, _⟩ => plane466GenDeadBound0001
  | ⟨2, _⟩ => plane466GenDeadBound0002
  | ⟨3, _⟩ => plane466GenDeadBound0003
  | ⟨4, _⟩ => plane466GenDeadBound0004
  | ⟨5, _⟩ => plane466GenDeadBound0005
  | ⟨6, _⟩ => plane466GenDeadBound0006
  | ⟨7, _⟩ => plane466GenDeadBound0007
  | ⟨8, _⟩ => plane466GenDeadBound0008
  | ⟨9, _⟩ => plane466GenDeadBound0009
  | ⟨10, _⟩ => plane466GenDeadBound0010
  | ⟨11, _⟩ => plane466GenDeadBound0011
  | ⟨12, _⟩ => plane466GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
