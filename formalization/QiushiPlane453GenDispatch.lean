import QiushiPlane453GenBindings00
import QiushiPlane453GenBindings01
import QiushiPlane453GenBindings02
import QiushiPlane453GenBindings03
import QiushiPlane453GenBindings04
import QiushiPlane453GenBindings05
import QiushiPlane453GenBindings06
import QiushiPlane453GenBindings07
import QiushiPlane453GenBindings08
import QiushiPlane453GenBindings09
import QiushiPlane453GenBindings10
import QiushiPlane453GenBindings11
import QiushiPlane453GenBindings12
import QiushiPlane453GenBindings13
import QiushiPlane453GenBindings14
import QiushiPlane453GenBindings15
import QiushiPlane453GenBindings16
import QiushiPlane453GenBindings17
import QiushiPlane453GenBindings18
import QiushiPlane453GenBindings19
import QiushiPlane453GenBindings20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane453GenSourceQRA (i : Fin 210) :
    QuotientRankAtLeast (spanCodes (plane453GenSourceBasis i)) (plane453GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane453GenBound0000
  | ⟨1, _⟩ => plane453GenBound0001
  | ⟨2, _⟩ => plane453GenBound0002
  | ⟨3, _⟩ => plane453GenBound0003
  | ⟨4, _⟩ => plane453GenBound0004
  | ⟨5, _⟩ => plane453GenBound0005
  | ⟨6, _⟩ => plane453GenBound0006
  | ⟨7, _⟩ => plane453GenBound0007
  | ⟨8, _⟩ => plane453GenBound0008
  | ⟨9, _⟩ => plane453GenBound0009
  | ⟨10, _⟩ => plane453GenBound0010
  | ⟨11, _⟩ => plane453GenBound0011
  | ⟨12, _⟩ => plane453GenBound0012
  | ⟨13, _⟩ => plane453GenBound0013
  | ⟨14, _⟩ => plane453GenBound0014
  | ⟨15, _⟩ => plane453GenBound0015
  | ⟨16, _⟩ => plane453GenBound0016
  | ⟨17, _⟩ => plane453GenBound0017
  | ⟨18, _⟩ => plane453GenBound0018
  | ⟨19, _⟩ => plane453GenBound0019
  | ⟨20, _⟩ => plane453GenBound0020
  | ⟨21, _⟩ => plane453GenBound0021
  | ⟨22, _⟩ => plane453GenBound0022
  | ⟨23, _⟩ => plane453GenBound0023
  | ⟨24, _⟩ => plane453GenBound0024
  | ⟨25, _⟩ => plane453GenBound0025
  | ⟨26, _⟩ => plane453GenBound0026
  | ⟨27, _⟩ => plane453GenBound0027
  | ⟨28, _⟩ => plane453GenBound0028
  | ⟨29, _⟩ => plane453GenBound0029
  | ⟨30, _⟩ => plane453GenBound0030
  | ⟨31, _⟩ => plane453GenBound0031
  | ⟨32, _⟩ => plane453GenBound0032
  | ⟨33, _⟩ => plane453GenBound0033
  | ⟨34, _⟩ => plane453GenBound0034
  | ⟨35, _⟩ => plane453GenBound0035
  | ⟨36, _⟩ => plane453GenBound0036
  | ⟨37, _⟩ => plane453GenBound0037
  | ⟨38, _⟩ => plane453GenBound0038
  | ⟨39, _⟩ => plane453GenBound0039
  | ⟨40, _⟩ => plane453GenBound0040
  | ⟨41, _⟩ => plane453GenBound0041
  | ⟨42, _⟩ => plane453GenBound0042
  | ⟨43, _⟩ => plane453GenBound0043
  | ⟨44, _⟩ => plane453GenBound0044
  | ⟨45, _⟩ => plane453GenBound0045
  | ⟨46, _⟩ => plane453GenBound0046
  | ⟨47, _⟩ => plane453GenBound0047
  | ⟨48, _⟩ => plane453GenBound0048
  | ⟨49, _⟩ => plane453GenBound0049
  | ⟨50, _⟩ => plane453GenBound0050
  | ⟨51, _⟩ => plane453GenBound0051
  | ⟨52, _⟩ => plane453GenBound0052
  | ⟨53, _⟩ => plane453GenBound0053
  | ⟨54, _⟩ => plane453GenBound0054
  | ⟨55, _⟩ => plane453GenBound0055
  | ⟨56, _⟩ => plane453GenBound0056
  | ⟨57, _⟩ => plane453GenBound0057
  | ⟨58, _⟩ => plane453GenBound0058
  | ⟨59, _⟩ => plane453GenBound0059
  | ⟨60, _⟩ => plane453GenBound0060
  | ⟨61, _⟩ => plane453GenBound0061
  | ⟨62, _⟩ => plane453GenBound0062
  | ⟨63, _⟩ => plane453GenBound0063
  | ⟨64, _⟩ => plane453GenBound0064
  | ⟨65, _⟩ => plane453GenBound0065
  | ⟨66, _⟩ => plane453GenBound0066
  | ⟨67, _⟩ => plane453GenBound0067
  | ⟨68, _⟩ => plane453GenBound0068
  | ⟨69, _⟩ => plane453GenBound0069
  | ⟨70, _⟩ => plane453GenBound0070
  | ⟨71, _⟩ => plane453GenBound0071
  | ⟨72, _⟩ => plane453GenBound0072
  | ⟨73, _⟩ => plane453GenBound0073
  | ⟨74, _⟩ => plane453GenBound0074
  | ⟨75, _⟩ => plane453GenBound0075
  | ⟨76, _⟩ => plane453GenBound0076
  | ⟨77, _⟩ => plane453GenBound0077
  | ⟨78, _⟩ => plane453GenBound0078
  | ⟨79, _⟩ => plane453GenBound0079
  | ⟨80, _⟩ => plane453GenBound0080
  | ⟨81, _⟩ => plane453GenBound0081
  | ⟨82, _⟩ => plane453GenBound0082
  | ⟨83, _⟩ => plane453GenBound0083
  | ⟨84, _⟩ => plane453GenBound0084
  | ⟨85, _⟩ => plane453GenBound0085
  | ⟨86, _⟩ => plane453GenBound0086
  | ⟨87, _⟩ => plane453GenBound0087
  | ⟨88, _⟩ => plane453GenBound0088
  | ⟨89, _⟩ => plane453GenBound0089
  | ⟨90, _⟩ => plane453GenBound0090
  | ⟨91, _⟩ => plane453GenBound0091
  | ⟨92, _⟩ => plane453GenBound0092
  | ⟨93, _⟩ => plane453GenBound0093
  | ⟨94, _⟩ => plane453GenBound0094
  | ⟨95, _⟩ => plane453GenBound0095
  | ⟨96, _⟩ => plane453GenBound0096
  | ⟨97, _⟩ => plane453GenBound0097
  | ⟨98, _⟩ => plane453GenBound0098
  | ⟨99, _⟩ => plane453GenBound0099
  | ⟨100, _⟩ => plane453GenBound0100
  | ⟨101, _⟩ => plane453GenBound0101
  | ⟨102, _⟩ => plane453GenBound0102
  | ⟨103, _⟩ => plane453GenBound0103
  | ⟨104, _⟩ => plane453GenBound0104
  | ⟨105, _⟩ => plane453GenBound0105
  | ⟨106, _⟩ => plane453GenBound0106
  | ⟨107, _⟩ => plane453GenBound0107
  | ⟨108, _⟩ => plane453GenBound0108
  | ⟨109, _⟩ => plane453GenBound0109
  | ⟨110, _⟩ => plane453GenBound0110
  | ⟨111, _⟩ => plane453GenBound0111
  | ⟨112, _⟩ => plane453GenBound0112
  | ⟨113, _⟩ => plane453GenBound0113
  | ⟨114, _⟩ => plane453GenBound0114
  | ⟨115, _⟩ => plane453GenBound0115
  | ⟨116, _⟩ => plane453GenBound0116
  | ⟨117, _⟩ => plane453GenBound0117
  | ⟨118, _⟩ => plane453GenBound0118
  | ⟨119, _⟩ => plane453GenBound0119
  | ⟨120, _⟩ => plane453GenBound0120
  | ⟨121, _⟩ => plane453GenBound0121
  | ⟨122, _⟩ => plane453GenBound0122
  | ⟨123, _⟩ => plane453GenBound0123
  | ⟨124, _⟩ => plane453GenBound0124
  | ⟨125, _⟩ => plane453GenBound0125
  | ⟨126, _⟩ => plane453GenBound0126
  | ⟨127, _⟩ => plane453GenBound0127
  | ⟨128, _⟩ => plane453GenBound0128
  | ⟨129, _⟩ => plane453GenBound0129
  | ⟨130, _⟩ => plane453GenBound0130
  | ⟨131, _⟩ => plane453GenBound0131
  | ⟨132, _⟩ => plane453GenBound0132
  | ⟨133, _⟩ => plane453GenBound0133
  | ⟨134, _⟩ => plane453GenBound0134
  | ⟨135, _⟩ => plane453GenBound0135
  | ⟨136, _⟩ => plane453GenBound0136
  | ⟨137, _⟩ => plane453GenBound0137
  | ⟨138, _⟩ => plane453GenBound0138
  | ⟨139, _⟩ => plane453GenBound0139
  | ⟨140, _⟩ => plane453GenBound0140
  | ⟨141, _⟩ => plane453GenBound0141
  | ⟨142, _⟩ => plane453GenBound0142
  | ⟨143, _⟩ => plane453GenBound0143
  | ⟨144, _⟩ => plane453GenBound0144
  | ⟨145, _⟩ => plane453GenBound0145
  | ⟨146, _⟩ => plane453GenBound0146
  | ⟨147, _⟩ => plane453GenBound0147
  | ⟨148, _⟩ => plane453GenBound0148
  | ⟨149, _⟩ => plane453GenBound0149
  | ⟨150, _⟩ => plane453GenBound0150
  | ⟨151, _⟩ => plane453GenBound0151
  | ⟨152, _⟩ => plane453GenBound0152
  | ⟨153, _⟩ => plane453GenBound0153
  | ⟨154, _⟩ => plane453GenBound0154
  | ⟨155, _⟩ => plane453GenBound0155
  | ⟨156, _⟩ => plane453GenBound0156
  | ⟨157, _⟩ => plane453GenBound0157
  | ⟨158, _⟩ => plane453GenBound0158
  | ⟨159, _⟩ => plane453GenBound0159
  | ⟨160, _⟩ => plane453GenBound0160
  | ⟨161, _⟩ => plane453GenBound0161
  | ⟨162, _⟩ => plane453GenBound0162
  | ⟨163, _⟩ => plane453GenBound0163
  | ⟨164, _⟩ => plane453GenBound0164
  | ⟨165, _⟩ => plane453GenBound0165
  | ⟨166, _⟩ => plane453GenBound0166
  | ⟨167, _⟩ => plane453GenBound0167
  | ⟨168, _⟩ => plane453GenBound0168
  | ⟨169, _⟩ => plane453GenBound0169
  | ⟨170, _⟩ => plane453GenBound0170
  | ⟨171, _⟩ => plane453GenBound0171
  | ⟨172, _⟩ => plane453GenBound0172
  | ⟨173, _⟩ => plane453GenBound0173
  | ⟨174, _⟩ => plane453GenBound0174
  | ⟨175, _⟩ => plane453GenBound0175
  | ⟨176, _⟩ => plane453GenBound0176
  | ⟨177, _⟩ => plane453GenBound0177
  | ⟨178, _⟩ => plane453GenBound0178
  | ⟨179, _⟩ => plane453GenBound0179
  | ⟨180, _⟩ => plane453GenBound0180
  | ⟨181, _⟩ => plane453GenBound0181
  | ⟨182, _⟩ => plane453GenBound0182
  | ⟨183, _⟩ => plane453GenBound0183
  | ⟨184, _⟩ => plane453GenBound0184
  | ⟨185, _⟩ => plane453GenBound0185
  | ⟨186, _⟩ => plane453GenBound0186
  | ⟨187, _⟩ => plane453GenBound0187
  | ⟨188, _⟩ => plane453GenBound0188
  | ⟨189, _⟩ => plane453GenBound0189
  | ⟨190, _⟩ => plane453GenBound0190
  | ⟨191, _⟩ => plane453GenBound0191
  | ⟨192, _⟩ => plane453GenBound0192
  | ⟨193, _⟩ => plane453GenBound0193
  | ⟨194, _⟩ => plane453GenBound0194
  | ⟨195, _⟩ => plane453GenBound0195
  | ⟨196, _⟩ => plane453GenBound0196
  | ⟨197, _⟩ => plane453GenBound0197
  | ⟨198, _⟩ => plane453GenBound0198
  | ⟨199, _⟩ => plane453GenBound0199
  | ⟨200, _⟩ => plane453GenBound0200
  | ⟨201, _⟩ => plane453GenBound0201
  | ⟨202, _⟩ => plane453GenBound0202
  | ⟨203, _⟩ => plane453GenBound0203
  | ⟨204, _⟩ => plane453GenBound0204
  | ⟨205, _⟩ => plane453GenBound0205
  | ⟨206, _⟩ => plane453GenBound0206
  | ⟨207, _⟩ => plane453GenBound0207
  | ⟨208, _⟩ => plane453GenBound0208
  | ⟨209, _⟩ => plane453GenBound0209
  | ⟨k + 210, h⟩ => by omega
theorem plane453GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (0 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (0 : Fin 13) = [68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0000 (by decide)
theorem plane453GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (1 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (1 : Fin 13) = [68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0001 (by decide)
theorem plane453GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (2 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (2 : Fin 13) = [131, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0002 (by decide)
theorem plane453GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (3 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (3 : Fin 13) = [133, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0003 (by decide)
theorem plane453GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (4 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (4 : Fin 13) = [160, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0004 (by decide)
theorem plane453GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (5 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (5 : Fin 13) = [262, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0005 (by decide)
theorem plane453GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (6 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (6 : Fin 13) = [263, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0006 (by decide)
theorem plane453GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (7 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (7 : Fin 13) = [290, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0007 (by decide)
theorem plane453GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (8 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (8 : Fin 13) = [293, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0008 (by decide)
theorem plane453GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (9 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (9 : Fin 13) = [386, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0009 (by decide)
theorem plane453GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (10 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (10 : Fin 13) = [389, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0010 (by decide)
theorem plane453GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (11 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (11 : Fin 13) = [422, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0011 (by decide)
theorem plane453GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis (12 : Fin 13))) 17 := by
  rw [show plane453GenDeadBasis (12 : Fin 13) = [423, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane453GenSource0012 (by decide)
theorem plane453GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane453GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane453GenDeadBound0000
  | ⟨1, _⟩ => plane453GenDeadBound0001
  | ⟨2, _⟩ => plane453GenDeadBound0002
  | ⟨3, _⟩ => plane453GenDeadBound0003
  | ⟨4, _⟩ => plane453GenDeadBound0004
  | ⟨5, _⟩ => plane453GenDeadBound0005
  | ⟨6, _⟩ => plane453GenDeadBound0006
  | ⟨7, _⟩ => plane453GenDeadBound0007
  | ⟨8, _⟩ => plane453GenDeadBound0008
  | ⟨9, _⟩ => plane453GenDeadBound0009
  | ⟨10, _⟩ => plane453GenDeadBound0010
  | ⟨11, _⟩ => plane453GenDeadBound0011
  | ⟨12, _⟩ => plane453GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
