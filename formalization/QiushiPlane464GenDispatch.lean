import QiushiPlane464GenBindings00
import QiushiPlane464GenBindings01
import QiushiPlane464GenBindings02
import QiushiPlane464GenBindings03
import QiushiPlane464GenBindings04
import QiushiPlane464GenBindings05
import QiushiPlane464GenBindings06
import QiushiPlane464GenBindings07
import QiushiPlane464GenBindings08
import QiushiPlane464GenBindings09
import QiushiPlane464GenBindings10
import QiushiPlane464GenBindings11
import QiushiPlane464GenBindings12
import QiushiPlane464GenBindings13
import QiushiPlane464GenBindings14
import QiushiPlane464GenBindings15
import QiushiPlane464GenBindings16
import QiushiPlane464GenBindings17
import QiushiPlane464GenBindings18
import QiushiPlane464GenBindings19
import QiushiPlane464GenBindings20
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane464GenSourceQRA (i : Fin 202) :
    QuotientRankAtLeast (spanCodes (plane464GenSourceBasis i)) (plane464GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane464GenBound0000
  | ⟨1, _⟩ => plane464GenBound0001
  | ⟨2, _⟩ => plane464GenBound0002
  | ⟨3, _⟩ => plane464GenBound0003
  | ⟨4, _⟩ => plane464GenBound0004
  | ⟨5, _⟩ => plane464GenBound0005
  | ⟨6, _⟩ => plane464GenBound0006
  | ⟨7, _⟩ => plane464GenBound0007
  | ⟨8, _⟩ => plane464GenBound0008
  | ⟨9, _⟩ => plane464GenBound0009
  | ⟨10, _⟩ => plane464GenBound0010
  | ⟨11, _⟩ => plane464GenBound0011
  | ⟨12, _⟩ => plane464GenBound0012
  | ⟨13, _⟩ => plane464GenBound0013
  | ⟨14, _⟩ => plane464GenBound0014
  | ⟨15, _⟩ => plane464GenBound0015
  | ⟨16, _⟩ => plane464GenBound0016
  | ⟨17, _⟩ => plane464GenBound0017
  | ⟨18, _⟩ => plane464GenBound0018
  | ⟨19, _⟩ => plane464GenBound0019
  | ⟨20, _⟩ => plane464GenBound0020
  | ⟨21, _⟩ => plane464GenBound0021
  | ⟨22, _⟩ => plane464GenBound0022
  | ⟨23, _⟩ => plane464GenBound0023
  | ⟨24, _⟩ => plane464GenBound0024
  | ⟨25, _⟩ => plane464GenBound0025
  | ⟨26, _⟩ => plane464GenBound0026
  | ⟨27, _⟩ => plane464GenBound0027
  | ⟨28, _⟩ => plane464GenBound0028
  | ⟨29, _⟩ => plane464GenBound0029
  | ⟨30, _⟩ => plane464GenBound0030
  | ⟨31, _⟩ => plane464GenBound0031
  | ⟨32, _⟩ => plane464GenBound0032
  | ⟨33, _⟩ => plane464GenBound0033
  | ⟨34, _⟩ => plane464GenBound0034
  | ⟨35, _⟩ => plane464GenBound0035
  | ⟨36, _⟩ => plane464GenBound0036
  | ⟨37, _⟩ => plane464GenBound0037
  | ⟨38, _⟩ => plane464GenBound0038
  | ⟨39, _⟩ => plane464GenBound0039
  | ⟨40, _⟩ => plane464GenBound0040
  | ⟨41, _⟩ => plane464GenBound0041
  | ⟨42, _⟩ => plane464GenBound0042
  | ⟨43, _⟩ => plane464GenBound0043
  | ⟨44, _⟩ => plane464GenBound0044
  | ⟨45, _⟩ => plane464GenBound0045
  | ⟨46, _⟩ => plane464GenBound0046
  | ⟨47, _⟩ => plane464GenBound0047
  | ⟨48, _⟩ => plane464GenBound0048
  | ⟨49, _⟩ => plane464GenBound0049
  | ⟨50, _⟩ => plane464GenBound0050
  | ⟨51, _⟩ => plane464GenBound0051
  | ⟨52, _⟩ => plane464GenBound0052
  | ⟨53, _⟩ => plane464GenBound0053
  | ⟨54, _⟩ => plane464GenBound0054
  | ⟨55, _⟩ => plane464GenBound0055
  | ⟨56, _⟩ => plane464GenBound0056
  | ⟨57, _⟩ => plane464GenBound0057
  | ⟨58, _⟩ => plane464GenBound0058
  | ⟨59, _⟩ => plane464GenBound0059
  | ⟨60, _⟩ => plane464GenBound0060
  | ⟨61, _⟩ => plane464GenBound0061
  | ⟨62, _⟩ => plane464GenBound0062
  | ⟨63, _⟩ => plane464GenBound0063
  | ⟨64, _⟩ => plane464GenBound0064
  | ⟨65, _⟩ => plane464GenBound0065
  | ⟨66, _⟩ => plane464GenBound0066
  | ⟨67, _⟩ => plane464GenBound0067
  | ⟨68, _⟩ => plane464GenBound0068
  | ⟨69, _⟩ => plane464GenBound0069
  | ⟨70, _⟩ => plane464GenBound0070
  | ⟨71, _⟩ => plane464GenBound0071
  | ⟨72, _⟩ => plane464GenBound0072
  | ⟨73, _⟩ => plane464GenBound0073
  | ⟨74, _⟩ => plane464GenBound0074
  | ⟨75, _⟩ => plane464GenBound0075
  | ⟨76, _⟩ => plane464GenBound0076
  | ⟨77, _⟩ => plane464GenBound0077
  | ⟨78, _⟩ => plane464GenBound0078
  | ⟨79, _⟩ => plane464GenBound0079
  | ⟨80, _⟩ => plane464GenBound0080
  | ⟨81, _⟩ => plane464GenBound0081
  | ⟨82, _⟩ => plane464GenBound0082
  | ⟨83, _⟩ => plane464GenBound0083
  | ⟨84, _⟩ => plane464GenBound0084
  | ⟨85, _⟩ => plane464GenBound0085
  | ⟨86, _⟩ => plane464GenBound0086
  | ⟨87, _⟩ => plane464GenBound0087
  | ⟨88, _⟩ => plane464GenBound0088
  | ⟨89, _⟩ => plane464GenBound0089
  | ⟨90, _⟩ => plane464GenBound0090
  | ⟨91, _⟩ => plane464GenBound0091
  | ⟨92, _⟩ => plane464GenBound0092
  | ⟨93, _⟩ => plane464GenBound0093
  | ⟨94, _⟩ => plane464GenBound0094
  | ⟨95, _⟩ => plane464GenBound0095
  | ⟨96, _⟩ => plane464GenBound0096
  | ⟨97, _⟩ => plane464GenBound0097
  | ⟨98, _⟩ => plane464GenBound0098
  | ⟨99, _⟩ => plane464GenBound0099
  | ⟨100, _⟩ => plane464GenBound0100
  | ⟨101, _⟩ => plane464GenBound0101
  | ⟨102, _⟩ => plane464GenBound0102
  | ⟨103, _⟩ => plane464GenBound0103
  | ⟨104, _⟩ => plane464GenBound0104
  | ⟨105, _⟩ => plane464GenBound0105
  | ⟨106, _⟩ => plane464GenBound0106
  | ⟨107, _⟩ => plane464GenBound0107
  | ⟨108, _⟩ => plane464GenBound0108
  | ⟨109, _⟩ => plane464GenBound0109
  | ⟨110, _⟩ => plane464GenBound0110
  | ⟨111, _⟩ => plane464GenBound0111
  | ⟨112, _⟩ => plane464GenBound0112
  | ⟨113, _⟩ => plane464GenBound0113
  | ⟨114, _⟩ => plane464GenBound0114
  | ⟨115, _⟩ => plane464GenBound0115
  | ⟨116, _⟩ => plane464GenBound0116
  | ⟨117, _⟩ => plane464GenBound0117
  | ⟨118, _⟩ => plane464GenBound0118
  | ⟨119, _⟩ => plane464GenBound0119
  | ⟨120, _⟩ => plane464GenBound0120
  | ⟨121, _⟩ => plane464GenBound0121
  | ⟨122, _⟩ => plane464GenBound0122
  | ⟨123, _⟩ => plane464GenBound0123
  | ⟨124, _⟩ => plane464GenBound0124
  | ⟨125, _⟩ => plane464GenBound0125
  | ⟨126, _⟩ => plane464GenBound0126
  | ⟨127, _⟩ => plane464GenBound0127
  | ⟨128, _⟩ => plane464GenBound0128
  | ⟨129, _⟩ => plane464GenBound0129
  | ⟨130, _⟩ => plane464GenBound0130
  | ⟨131, _⟩ => plane464GenBound0131
  | ⟨132, _⟩ => plane464GenBound0132
  | ⟨133, _⟩ => plane464GenBound0133
  | ⟨134, _⟩ => plane464GenBound0134
  | ⟨135, _⟩ => plane464GenBound0135
  | ⟨136, _⟩ => plane464GenBound0136
  | ⟨137, _⟩ => plane464GenBound0137
  | ⟨138, _⟩ => plane464GenBound0138
  | ⟨139, _⟩ => plane464GenBound0139
  | ⟨140, _⟩ => plane464GenBound0140
  | ⟨141, _⟩ => plane464GenBound0141
  | ⟨142, _⟩ => plane464GenBound0142
  | ⟨143, _⟩ => plane464GenBound0143
  | ⟨144, _⟩ => plane464GenBound0144
  | ⟨145, _⟩ => plane464GenBound0145
  | ⟨146, _⟩ => plane464GenBound0146
  | ⟨147, _⟩ => plane464GenBound0147
  | ⟨148, _⟩ => plane464GenBound0148
  | ⟨149, _⟩ => plane464GenBound0149
  | ⟨150, _⟩ => plane464GenBound0150
  | ⟨151, _⟩ => plane464GenBound0151
  | ⟨152, _⟩ => plane464GenBound0152
  | ⟨153, _⟩ => plane464GenBound0153
  | ⟨154, _⟩ => plane464GenBound0154
  | ⟨155, _⟩ => plane464GenBound0155
  | ⟨156, _⟩ => plane464GenBound0156
  | ⟨157, _⟩ => plane464GenBound0157
  | ⟨158, _⟩ => plane464GenBound0158
  | ⟨159, _⟩ => plane464GenBound0159
  | ⟨160, _⟩ => plane464GenBound0160
  | ⟨161, _⟩ => plane464GenBound0161
  | ⟨162, _⟩ => plane464GenBound0162
  | ⟨163, _⟩ => plane464GenBound0163
  | ⟨164, _⟩ => plane464GenBound0164
  | ⟨165, _⟩ => plane464GenBound0165
  | ⟨166, _⟩ => plane464GenBound0166
  | ⟨167, _⟩ => plane464GenBound0167
  | ⟨168, _⟩ => plane464GenBound0168
  | ⟨169, _⟩ => plane464GenBound0169
  | ⟨170, _⟩ => plane464GenBound0170
  | ⟨171, _⟩ => plane464GenBound0171
  | ⟨172, _⟩ => plane464GenBound0172
  | ⟨173, _⟩ => plane464GenBound0173
  | ⟨174, _⟩ => plane464GenBound0174
  | ⟨175, _⟩ => plane464GenBound0175
  | ⟨176, _⟩ => plane464GenBound0176
  | ⟨177, _⟩ => plane464GenBound0177
  | ⟨178, _⟩ => plane464GenBound0178
  | ⟨179, _⟩ => plane464GenBound0179
  | ⟨180, _⟩ => plane464GenBound0180
  | ⟨181, _⟩ => plane464GenBound0181
  | ⟨182, _⟩ => plane464GenBound0182
  | ⟨183, _⟩ => plane464GenBound0183
  | ⟨184, _⟩ => plane464GenBound0184
  | ⟨185, _⟩ => plane464GenBound0185
  | ⟨186, _⟩ => plane464GenBound0186
  | ⟨187, _⟩ => plane464GenBound0187
  | ⟨188, _⟩ => plane464GenBound0188
  | ⟨189, _⟩ => plane464GenBound0189
  | ⟨190, _⟩ => plane464GenBound0190
  | ⟨191, _⟩ => plane464GenBound0191
  | ⟨192, _⟩ => plane464GenBound0192
  | ⟨193, _⟩ => plane464GenBound0193
  | ⟨194, _⟩ => plane464GenBound0194
  | ⟨195, _⟩ => plane464GenBound0195
  | ⟨196, _⟩ => plane464GenBound0196
  | ⟨197, _⟩ => plane464GenBound0197
  | ⟨198, _⟩ => plane464GenBound0198
  | ⟨199, _⟩ => plane464GenBound0199
  | ⟨200, _⟩ => plane464GenBound0200
  | ⟨201, _⟩ => plane464GenBound0201
  | ⟨k + 202, h⟩ => by omega
theorem plane464GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (0 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (0 : Fin 13) = [160, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0000 (by decide)
theorem plane464GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (1 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (1 : Fin 13) = [151, 68, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0001 (by decide)
theorem plane464GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (2 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (2 : Fin 13) = [145, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0002 (by decide)
theorem plane464GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (3 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (3 : Fin 13) = [133, 68, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0003 (by decide)
theorem plane464GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (4 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (4 : Fin 13) = [131, 68, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0004 (by decide)
theorem plane464GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (5 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (5 : Fin 13) = [262, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0005 (by decide)
theorem plane464GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (6 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (6 : Fin 13) = [263, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0006 (by decide)
theorem plane464GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (7 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (7 : Fin 13) = [274, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0007 (by decide)
theorem plane464GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (8 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (8 : Fin 13) = [275, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0008 (by decide)
theorem plane464GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (9 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (9 : Fin 13) = [290, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0009 (by decide)
theorem plane464GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (10 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (10 : Fin 13) = [293, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0010 (by decide)
theorem plane464GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (11 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (11 : Fin 13) = [305, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0011 (by decide)
theorem plane464GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis (12 : Fin 13))) 17 := by
  rw [show plane464GenDeadBasis (12 : Fin 13) = [310, 180, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane464GenSource0012 (by decide)
theorem plane464GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane464GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane464GenDeadBound0000
  | ⟨1, _⟩ => plane464GenDeadBound0001
  | ⟨2, _⟩ => plane464GenDeadBound0002
  | ⟨3, _⟩ => plane464GenDeadBound0003
  | ⟨4, _⟩ => plane464GenDeadBound0004
  | ⟨5, _⟩ => plane464GenDeadBound0005
  | ⟨6, _⟩ => plane464GenDeadBound0006
  | ⟨7, _⟩ => plane464GenDeadBound0007
  | ⟨8, _⟩ => plane464GenDeadBound0008
  | ⟨9, _⟩ => plane464GenDeadBound0009
  | ⟨10, _⟩ => plane464GenDeadBound0010
  | ⟨11, _⟩ => plane464GenDeadBound0011
  | ⟨12, _⟩ => plane464GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
