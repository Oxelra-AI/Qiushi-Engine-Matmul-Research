import QiushiPlane480GenBindings00
import QiushiPlane480GenBindings01
import QiushiPlane480GenBindings02
import QiushiPlane480GenBindings03
import QiushiPlane480GenBindings04
import QiushiPlane480GenBindings05
import QiushiPlane480GenBindings06
import QiushiPlane480GenBindings07
import QiushiPlane480GenBindings08
import QiushiPlane480GenBindings09
import QiushiPlane480GenBindings10
import QiushiPlane480GenBindings11
import QiushiPlane480GenBindings12
import QiushiPlane480GenBindings13
import QiushiPlane480GenBindings14
import QiushiPlane480GenBindings15
import QiushiPlane480GenBindings16
import QiushiPlane480GenBindings17
import QiushiPlane480GenBindings18
import QiushiPlane480GenBindings19
import QiushiPlane480GenBindings20
import QiushiPlane480GenBindings21
import QiushiPlane480GenBindings22
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane480GenSourceQRA (i : Fin 221) :
    QuotientRankAtLeast (spanCodes (plane480GenSourceBasis i)) (plane480GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane480GenBound0000
  | ⟨1, _⟩ => plane480GenBound0001
  | ⟨2, _⟩ => plane480GenBound0002
  | ⟨3, _⟩ => plane480GenBound0003
  | ⟨4, _⟩ => plane480GenBound0004
  | ⟨5, _⟩ => plane480GenBound0005
  | ⟨6, _⟩ => plane480GenBound0006
  | ⟨7, _⟩ => plane480GenBound0007
  | ⟨8, _⟩ => plane480GenBound0008
  | ⟨9, _⟩ => plane480GenBound0009
  | ⟨10, _⟩ => plane480GenBound0010
  | ⟨11, _⟩ => plane480GenBound0011
  | ⟨12, _⟩ => plane480GenBound0012
  | ⟨13, _⟩ => plane480GenBound0013
  | ⟨14, _⟩ => plane480GenBound0014
  | ⟨15, _⟩ => plane480GenBound0015
  | ⟨16, _⟩ => plane480GenBound0016
  | ⟨17, _⟩ => plane480GenBound0017
  | ⟨18, _⟩ => plane480GenBound0018
  | ⟨19, _⟩ => plane480GenBound0019
  | ⟨20, _⟩ => plane480GenBound0020
  | ⟨21, _⟩ => plane480GenBound0021
  | ⟨22, _⟩ => plane480GenBound0022
  | ⟨23, _⟩ => plane480GenBound0023
  | ⟨24, _⟩ => plane480GenBound0024
  | ⟨25, _⟩ => plane480GenBound0025
  | ⟨26, _⟩ => plane480GenBound0026
  | ⟨27, _⟩ => plane480GenBound0027
  | ⟨28, _⟩ => plane480GenBound0028
  | ⟨29, _⟩ => plane480GenBound0029
  | ⟨30, _⟩ => plane480GenBound0030
  | ⟨31, _⟩ => plane480GenBound0031
  | ⟨32, _⟩ => plane480GenBound0032
  | ⟨33, _⟩ => plane480GenBound0033
  | ⟨34, _⟩ => plane480GenBound0034
  | ⟨35, _⟩ => plane480GenBound0035
  | ⟨36, _⟩ => plane480GenBound0036
  | ⟨37, _⟩ => plane480GenBound0037
  | ⟨38, _⟩ => plane480GenBound0038
  | ⟨39, _⟩ => plane480GenBound0039
  | ⟨40, _⟩ => plane480GenBound0040
  | ⟨41, _⟩ => plane480GenBound0041
  | ⟨42, _⟩ => plane480GenBound0042
  | ⟨43, _⟩ => plane480GenBound0043
  | ⟨44, _⟩ => plane480GenBound0044
  | ⟨45, _⟩ => plane480GenBound0045
  | ⟨46, _⟩ => plane480GenBound0046
  | ⟨47, _⟩ => plane480GenBound0047
  | ⟨48, _⟩ => plane480GenBound0048
  | ⟨49, _⟩ => plane480GenBound0049
  | ⟨50, _⟩ => plane480GenBound0050
  | ⟨51, _⟩ => plane480GenBound0051
  | ⟨52, _⟩ => plane480GenBound0052
  | ⟨53, _⟩ => plane480GenBound0053
  | ⟨54, _⟩ => plane480GenBound0054
  | ⟨55, _⟩ => plane480GenBound0055
  | ⟨56, _⟩ => plane480GenBound0056
  | ⟨57, _⟩ => plane480GenBound0057
  | ⟨58, _⟩ => plane480GenBound0058
  | ⟨59, _⟩ => plane480GenBound0059
  | ⟨60, _⟩ => plane480GenBound0060
  | ⟨61, _⟩ => plane480GenBound0061
  | ⟨62, _⟩ => plane480GenBound0062
  | ⟨63, _⟩ => plane480GenBound0063
  | ⟨64, _⟩ => plane480GenBound0064
  | ⟨65, _⟩ => plane480GenBound0065
  | ⟨66, _⟩ => plane480GenBound0066
  | ⟨67, _⟩ => plane480GenBound0067
  | ⟨68, _⟩ => plane480GenBound0068
  | ⟨69, _⟩ => plane480GenBound0069
  | ⟨70, _⟩ => plane480GenBound0070
  | ⟨71, _⟩ => plane480GenBound0071
  | ⟨72, _⟩ => plane480GenBound0072
  | ⟨73, _⟩ => plane480GenBound0073
  | ⟨74, _⟩ => plane480GenBound0074
  | ⟨75, _⟩ => plane480GenBound0075
  | ⟨76, _⟩ => plane480GenBound0076
  | ⟨77, _⟩ => plane480GenBound0077
  | ⟨78, _⟩ => plane480GenBound0078
  | ⟨79, _⟩ => plane480GenBound0079
  | ⟨80, _⟩ => plane480GenBound0080
  | ⟨81, _⟩ => plane480GenBound0081
  | ⟨82, _⟩ => plane480GenBound0082
  | ⟨83, _⟩ => plane480GenBound0083
  | ⟨84, _⟩ => plane480GenBound0084
  | ⟨85, _⟩ => plane480GenBound0085
  | ⟨86, _⟩ => plane480GenBound0086
  | ⟨87, _⟩ => plane480GenBound0087
  | ⟨88, _⟩ => plane480GenBound0088
  | ⟨89, _⟩ => plane480GenBound0089
  | ⟨90, _⟩ => plane480GenBound0090
  | ⟨91, _⟩ => plane480GenBound0091
  | ⟨92, _⟩ => plane480GenBound0092
  | ⟨93, _⟩ => plane480GenBound0093
  | ⟨94, _⟩ => plane480GenBound0094
  | ⟨95, _⟩ => plane480GenBound0095
  | ⟨96, _⟩ => plane480GenBound0096
  | ⟨97, _⟩ => plane480GenBound0097
  | ⟨98, _⟩ => plane480GenBound0098
  | ⟨99, _⟩ => plane480GenBound0099
  | ⟨100, _⟩ => plane480GenBound0100
  | ⟨101, _⟩ => plane480GenBound0101
  | ⟨102, _⟩ => plane480GenBound0102
  | ⟨103, _⟩ => plane480GenBound0103
  | ⟨104, _⟩ => plane480GenBound0104
  | ⟨105, _⟩ => plane480GenBound0105
  | ⟨106, _⟩ => plane480GenBound0106
  | ⟨107, _⟩ => plane480GenBound0107
  | ⟨108, _⟩ => plane480GenBound0108
  | ⟨109, _⟩ => plane480GenBound0109
  | ⟨110, _⟩ => plane480GenBound0110
  | ⟨111, _⟩ => plane480GenBound0111
  | ⟨112, _⟩ => plane480GenBound0112
  | ⟨113, _⟩ => plane480GenBound0113
  | ⟨114, _⟩ => plane480GenBound0114
  | ⟨115, _⟩ => plane480GenBound0115
  | ⟨116, _⟩ => plane480GenBound0116
  | ⟨117, _⟩ => plane480GenBound0117
  | ⟨118, _⟩ => plane480GenBound0118
  | ⟨119, _⟩ => plane480GenBound0119
  | ⟨120, _⟩ => plane480GenBound0120
  | ⟨121, _⟩ => plane480GenBound0121
  | ⟨122, _⟩ => plane480GenBound0122
  | ⟨123, _⟩ => plane480GenBound0123
  | ⟨124, _⟩ => plane480GenBound0124
  | ⟨125, _⟩ => plane480GenBound0125
  | ⟨126, _⟩ => plane480GenBound0126
  | ⟨127, _⟩ => plane480GenBound0127
  | ⟨128, _⟩ => plane480GenBound0128
  | ⟨129, _⟩ => plane480GenBound0129
  | ⟨130, _⟩ => plane480GenBound0130
  | ⟨131, _⟩ => plane480GenBound0131
  | ⟨132, _⟩ => plane480GenBound0132
  | ⟨133, _⟩ => plane480GenBound0133
  | ⟨134, _⟩ => plane480GenBound0134
  | ⟨135, _⟩ => plane480GenBound0135
  | ⟨136, _⟩ => plane480GenBound0136
  | ⟨137, _⟩ => plane480GenBound0137
  | ⟨138, _⟩ => plane480GenBound0138
  | ⟨139, _⟩ => plane480GenBound0139
  | ⟨140, _⟩ => plane480GenBound0140
  | ⟨141, _⟩ => plane480GenBound0141
  | ⟨142, _⟩ => plane480GenBound0142
  | ⟨143, _⟩ => plane480GenBound0143
  | ⟨144, _⟩ => plane480GenBound0144
  | ⟨145, _⟩ => plane480GenBound0145
  | ⟨146, _⟩ => plane480GenBound0146
  | ⟨147, _⟩ => plane480GenBound0147
  | ⟨148, _⟩ => plane480GenBound0148
  | ⟨149, _⟩ => plane480GenBound0149
  | ⟨150, _⟩ => plane480GenBound0150
  | ⟨151, _⟩ => plane480GenBound0151
  | ⟨152, _⟩ => plane480GenBound0152
  | ⟨153, _⟩ => plane480GenBound0153
  | ⟨154, _⟩ => plane480GenBound0154
  | ⟨155, _⟩ => plane480GenBound0155
  | ⟨156, _⟩ => plane480GenBound0156
  | ⟨157, _⟩ => plane480GenBound0157
  | ⟨158, _⟩ => plane480GenBound0158
  | ⟨159, _⟩ => plane480GenBound0159
  | ⟨160, _⟩ => plane480GenBound0160
  | ⟨161, _⟩ => plane480GenBound0161
  | ⟨162, _⟩ => plane480GenBound0162
  | ⟨163, _⟩ => plane480GenBound0163
  | ⟨164, _⟩ => plane480GenBound0164
  | ⟨165, _⟩ => plane480GenBound0165
  | ⟨166, _⟩ => plane480GenBound0166
  | ⟨167, _⟩ => plane480GenBound0167
  | ⟨168, _⟩ => plane480GenBound0168
  | ⟨169, _⟩ => plane480GenBound0169
  | ⟨170, _⟩ => plane480GenBound0170
  | ⟨171, _⟩ => plane480GenBound0171
  | ⟨172, _⟩ => plane480GenBound0172
  | ⟨173, _⟩ => plane480GenBound0173
  | ⟨174, _⟩ => plane480GenBound0174
  | ⟨175, _⟩ => plane480GenBound0175
  | ⟨176, _⟩ => plane480GenBound0176
  | ⟨177, _⟩ => plane480GenBound0177
  | ⟨178, _⟩ => plane480GenBound0178
  | ⟨179, _⟩ => plane480GenBound0179
  | ⟨180, _⟩ => plane480GenBound0180
  | ⟨181, _⟩ => plane480GenBound0181
  | ⟨182, _⟩ => plane480GenBound0182
  | ⟨183, _⟩ => plane480GenBound0183
  | ⟨184, _⟩ => plane480GenBound0184
  | ⟨185, _⟩ => plane480GenBound0185
  | ⟨186, _⟩ => plane480GenBound0186
  | ⟨187, _⟩ => plane480GenBound0187
  | ⟨188, _⟩ => plane480GenBound0188
  | ⟨189, _⟩ => plane480GenBound0189
  | ⟨190, _⟩ => plane480GenBound0190
  | ⟨191, _⟩ => plane480GenBound0191
  | ⟨192, _⟩ => plane480GenBound0192
  | ⟨193, _⟩ => plane480GenBound0193
  | ⟨194, _⟩ => plane480GenBound0194
  | ⟨195, _⟩ => plane480GenBound0195
  | ⟨196, _⟩ => plane480GenBound0196
  | ⟨197, _⟩ => plane480GenBound0197
  | ⟨198, _⟩ => plane480GenBound0198
  | ⟨199, _⟩ => plane480GenBound0199
  | ⟨200, _⟩ => plane480GenBound0200
  | ⟨201, _⟩ => plane480GenBound0201
  | ⟨202, _⟩ => plane480GenBound0202
  | ⟨203, _⟩ => plane480GenBound0203
  | ⟨204, _⟩ => plane480GenBound0204
  | ⟨205, _⟩ => plane480GenBound0205
  | ⟨206, _⟩ => plane480GenBound0206
  | ⟨207, _⟩ => plane480GenBound0207
  | ⟨208, _⟩ => plane480GenBound0208
  | ⟨209, _⟩ => plane480GenBound0209
  | ⟨210, _⟩ => plane480GenBound0210
  | ⟨211, _⟩ => plane480GenBound0211
  | ⟨212, _⟩ => plane480GenBound0212
  | ⟨213, _⟩ => plane480GenBound0213
  | ⟨214, _⟩ => plane480GenBound0214
  | ⟨215, _⟩ => plane480GenBound0215
  | ⟨216, _⟩ => plane480GenBound0216
  | ⟨217, _⟩ => plane480GenBound0217
  | ⟨218, _⟩ => plane480GenBound0218
  | ⟨219, _⟩ => plane480GenBound0219
  | ⟨220, _⟩ => plane480GenBound0220
  | ⟨k + 221, h⟩ => by omega
theorem plane480GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (0 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (0 : Fin 101) = [16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0000 (by decide)
theorem plane480GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (1 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (1 : Fin 101) = [16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0001 (by decide)
theorem plane480GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (2 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (2 : Fin 101) = [16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0002 (by decide)
theorem plane480GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (3 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (3 : Fin 101) = [34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0003 (by decide)
theorem plane480GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (4 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (4 : Fin 101) = [36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0004 (by decide)
theorem plane480GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (5 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (5 : Fin 101) = [38, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0005 (by decide)
theorem plane480GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (6 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (6 : Fin 101) = [42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0006 (by decide)
theorem plane480GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (7 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (7 : Fin 101) = [44, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0007 (by decide)
theorem plane480GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (8 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (8 : Fin 101) = [46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0008 (by decide)
theorem plane480GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (9 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (9 : Fin 101) = [66, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0009 (by decide)
theorem plane480GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (10 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (10 : Fin 101) = [68, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0010 (by decide)
theorem plane480GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (11 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (11 : Fin 101) = [70, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0011 (by decide)
theorem plane480GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (12 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (12 : Fin 101) = [74, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0012 (by decide)
theorem plane480GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (13 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (13 : Fin 101) = [76, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0013 (by decide)
theorem plane480GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (14 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (14 : Fin 101) = [78, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0014 (by decide)
theorem plane480GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (15 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (15 : Fin 101) = [96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0015 (by decide)
theorem plane480GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (16 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (16 : Fin 101) = [98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0016 (by decide)
theorem plane480GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (17 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (17 : Fin 101) = [100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0017 (by decide)
theorem plane480GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (18 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (18 : Fin 101) = [102, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0018 (by decide)
theorem plane480GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (19 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (19 : Fin 101) = [104, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0019 (by decide)
theorem plane480GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (20 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (20 : Fin 101) = [106, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0020 (by decide)
theorem plane480GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (21 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (21 : Fin 101) = [108, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0021 (by decide)
theorem plane480GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (22 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (22 : Fin 101) = [110, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0022 (by decide)
theorem plane480GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (23 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (23 : Fin 101) = [132, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0023 (by decide)
theorem plane480GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (24 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (24 : Fin 101) = [134, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0024 (by decide)
theorem plane480GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (25 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (25 : Fin 101) = [136, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0025 (by decide)
theorem plane480GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (26 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (26 : Fin 101) = [138, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0026 (by decide)
theorem plane480GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (27 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (27 : Fin 101) = [140, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0027 (by decide)
theorem plane480GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (28 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (28 : Fin 101) = [142, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0028 (by decide)
theorem plane480GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (29 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (29 : Fin 101) = [160, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0029 (by decide)
theorem plane480GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (30 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (30 : Fin 101) = [162, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0030 (by decide)
theorem plane480GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (31 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (31 : Fin 101) = [164, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0031 (by decide)
theorem plane480GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (32 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (32 : Fin 101) = [166, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0032 (by decide)
theorem plane480GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (33 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (33 : Fin 101) = [168, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0033 (by decide)
theorem plane480GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (34 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (34 : Fin 101) = [170, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0034 (by decide)
theorem plane480GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (35 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (35 : Fin 101) = [172, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0035 (by decide)
theorem plane480GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (36 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (36 : Fin 101) = [174, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0036 (by decide)
theorem plane480GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (37 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (37 : Fin 101) = [192, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0037 (by decide)
theorem plane480GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (38 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (38 : Fin 101) = [194, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0038 (by decide)
theorem plane480GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (39 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (39 : Fin 101) = [196, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0039 (by decide)
theorem plane480GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (40 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (40 : Fin 101) = [198, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0040 (by decide)
theorem plane480GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (41 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (41 : Fin 101) = [200, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0041 (by decide)
theorem plane480GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (42 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (42 : Fin 101) = [202, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0042 (by decide)
theorem plane480GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (43 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (43 : Fin 101) = [204, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0043 (by decide)
theorem plane480GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (44 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (44 : Fin 101) = [206, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0044 (by decide)
theorem plane480GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (45 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (45 : Fin 101) = [224, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0045 (by decide)
theorem plane480GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (46 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (46 : Fin 101) = [226, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0046 (by decide)
theorem plane480GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (47 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (47 : Fin 101) = [228, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0047 (by decide)
theorem plane480GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (48 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (48 : Fin 101) = [230, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0048 (by decide)
theorem plane480GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (49 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (49 : Fin 101) = [232, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0049 (by decide)
theorem plane480GenDeadBound0050 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (50 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (50 : Fin 101) = [234, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0050 (by decide)
theorem plane480GenDeadBound0051 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (51 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (51 : Fin 101) = [236, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0051 (by decide)
theorem plane480GenDeadBound0052 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (52 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (52 : Fin 101) = [238, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0052 (by decide)
theorem plane480GenDeadBound0053 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (53 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (53 : Fin 101) = [258, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0053 (by decide)
theorem plane480GenDeadBound0054 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (54 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (54 : Fin 101) = [262, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0054 (by decide)
theorem plane480GenDeadBound0055 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (55 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (55 : Fin 101) = [264, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0055 (by decide)
theorem plane480GenDeadBound0056 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (56 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (56 : Fin 101) = [266, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0056 (by decide)
theorem plane480GenDeadBound0057 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (57 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (57 : Fin 101) = [268, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0057 (by decide)
theorem plane480GenDeadBound0058 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (58 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (58 : Fin 101) = [270, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0058 (by decide)
theorem plane480GenDeadBound0059 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (59 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (59 : Fin 101) = [290, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0059 (by decide)
theorem plane480GenDeadBound0060 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (60 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (60 : Fin 101) = [294, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0060 (by decide)
theorem plane480GenDeadBound0061 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (61 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (61 : Fin 101) = [296, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0061 (by decide)
theorem plane480GenDeadBound0062 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (62 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (62 : Fin 101) = [298, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0062 (by decide)
theorem plane480GenDeadBound0063 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (63 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (63 : Fin 101) = [300, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0063 (by decide)
theorem plane480GenDeadBound0064 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (64 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (64 : Fin 101) = [302, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0064 (by decide)
theorem plane480GenDeadBound0065 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (65 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (65 : Fin 101) = [322, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0065 (by decide)
theorem plane480GenDeadBound0066 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (66 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (66 : Fin 101) = [326, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0066 (by decide)
theorem plane480GenDeadBound0067 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (67 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (67 : Fin 101) = [328, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0067 (by decide)
theorem plane480GenDeadBound0068 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (68 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (68 : Fin 101) = [330, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0068 (by decide)
theorem plane480GenDeadBound0069 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (69 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (69 : Fin 101) = [332, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0069 (by decide)
theorem plane480GenDeadBound0070 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (70 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (70 : Fin 101) = [334, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0070 (by decide)
theorem plane480GenDeadBound0071 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (71 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (71 : Fin 101) = [352, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0071 (by decide)
theorem plane480GenDeadBound0072 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (72 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (72 : Fin 101) = [354, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0072 (by decide)
theorem plane480GenDeadBound0073 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (73 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (73 : Fin 101) = [356, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0073 (by decide)
theorem plane480GenDeadBound0074 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (74 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (74 : Fin 101) = [358, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0074 (by decide)
theorem plane480GenDeadBound0075 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (75 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (75 : Fin 101) = [362, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0075 (by decide)
theorem plane480GenDeadBound0076 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (76 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (76 : Fin 101) = [366, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0076 (by decide)
theorem plane480GenDeadBound0077 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (77 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (77 : Fin 101) = [386, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0077 (by decide)
theorem plane480GenDeadBound0078 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (78 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (78 : Fin 101) = [388, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0078 (by decide)
theorem plane480GenDeadBound0079 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (79 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (79 : Fin 101) = [392, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0079 (by decide)
theorem plane480GenDeadBound0080 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (80 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (80 : Fin 101) = [394, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0080 (by decide)
theorem plane480GenDeadBound0081 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (81 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (81 : Fin 101) = [396, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0081 (by decide)
theorem plane480GenDeadBound0082 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (82 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (82 : Fin 101) = [398, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0082 (by decide)
theorem plane480GenDeadBound0083 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (83 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (83 : Fin 101) = [418, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0083 (by decide)
theorem plane480GenDeadBound0084 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (84 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (84 : Fin 101) = [420, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0084 (by decide)
theorem plane480GenDeadBound0085 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (85 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (85 : Fin 101) = [424, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0085 (by decide)
theorem plane480GenDeadBound0086 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (86 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (86 : Fin 101) = [426, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0086 (by decide)
theorem plane480GenDeadBound0087 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (87 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (87 : Fin 101) = [428, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0087 (by decide)
theorem plane480GenDeadBound0088 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (88 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (88 : Fin 101) = [430, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0088 (by decide)
theorem plane480GenDeadBound0089 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (89 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (89 : Fin 101) = [450, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0089 (by decide)
theorem plane480GenDeadBound0090 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (90 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (90 : Fin 101) = [452, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0090 (by decide)
theorem plane480GenDeadBound0091 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (91 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (91 : Fin 101) = [456, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0091 (by decide)
theorem plane480GenDeadBound0092 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (92 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (92 : Fin 101) = [458, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0092 (by decide)
theorem plane480GenDeadBound0093 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (93 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (93 : Fin 101) = [460, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0093 (by decide)
theorem plane480GenDeadBound0094 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (94 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (94 : Fin 101) = [462, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0094 (by decide)
theorem plane480GenDeadBound0095 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (95 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (95 : Fin 101) = [480, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0095 (by decide)
theorem plane480GenDeadBound0096 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (96 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (96 : Fin 101) = [482, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0096 (by decide)
theorem plane480GenDeadBound0097 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (97 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (97 : Fin 101) = [484, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0097 (by decide)
theorem plane480GenDeadBound0098 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (98 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (98 : Fin 101) = [486, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0098 (by decide)
theorem plane480GenDeadBound0099 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (99 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (99 : Fin 101) = [490, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0099 (by decide)
theorem plane480GenDeadBound0100 :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis (100 : Fin 101))) 17 := by
  rw [show plane480GenDeadBasis (100 : Fin 101) = [492, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane480GenSource0100 (by decide)
theorem plane480GenDeadQRA (d : Fin 101) :
    QuotientRankAtLeast (spanCodes (plane480GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane480GenDeadBound0000
  | ⟨1, _⟩ => plane480GenDeadBound0001
  | ⟨2, _⟩ => plane480GenDeadBound0002
  | ⟨3, _⟩ => plane480GenDeadBound0003
  | ⟨4, _⟩ => plane480GenDeadBound0004
  | ⟨5, _⟩ => plane480GenDeadBound0005
  | ⟨6, _⟩ => plane480GenDeadBound0006
  | ⟨7, _⟩ => plane480GenDeadBound0007
  | ⟨8, _⟩ => plane480GenDeadBound0008
  | ⟨9, _⟩ => plane480GenDeadBound0009
  | ⟨10, _⟩ => plane480GenDeadBound0010
  | ⟨11, _⟩ => plane480GenDeadBound0011
  | ⟨12, _⟩ => plane480GenDeadBound0012
  | ⟨13, _⟩ => plane480GenDeadBound0013
  | ⟨14, _⟩ => plane480GenDeadBound0014
  | ⟨15, _⟩ => plane480GenDeadBound0015
  | ⟨16, _⟩ => plane480GenDeadBound0016
  | ⟨17, _⟩ => plane480GenDeadBound0017
  | ⟨18, _⟩ => plane480GenDeadBound0018
  | ⟨19, _⟩ => plane480GenDeadBound0019
  | ⟨20, _⟩ => plane480GenDeadBound0020
  | ⟨21, _⟩ => plane480GenDeadBound0021
  | ⟨22, _⟩ => plane480GenDeadBound0022
  | ⟨23, _⟩ => plane480GenDeadBound0023
  | ⟨24, _⟩ => plane480GenDeadBound0024
  | ⟨25, _⟩ => plane480GenDeadBound0025
  | ⟨26, _⟩ => plane480GenDeadBound0026
  | ⟨27, _⟩ => plane480GenDeadBound0027
  | ⟨28, _⟩ => plane480GenDeadBound0028
  | ⟨29, _⟩ => plane480GenDeadBound0029
  | ⟨30, _⟩ => plane480GenDeadBound0030
  | ⟨31, _⟩ => plane480GenDeadBound0031
  | ⟨32, _⟩ => plane480GenDeadBound0032
  | ⟨33, _⟩ => plane480GenDeadBound0033
  | ⟨34, _⟩ => plane480GenDeadBound0034
  | ⟨35, _⟩ => plane480GenDeadBound0035
  | ⟨36, _⟩ => plane480GenDeadBound0036
  | ⟨37, _⟩ => plane480GenDeadBound0037
  | ⟨38, _⟩ => plane480GenDeadBound0038
  | ⟨39, _⟩ => plane480GenDeadBound0039
  | ⟨40, _⟩ => plane480GenDeadBound0040
  | ⟨41, _⟩ => plane480GenDeadBound0041
  | ⟨42, _⟩ => plane480GenDeadBound0042
  | ⟨43, _⟩ => plane480GenDeadBound0043
  | ⟨44, _⟩ => plane480GenDeadBound0044
  | ⟨45, _⟩ => plane480GenDeadBound0045
  | ⟨46, _⟩ => plane480GenDeadBound0046
  | ⟨47, _⟩ => plane480GenDeadBound0047
  | ⟨48, _⟩ => plane480GenDeadBound0048
  | ⟨49, _⟩ => plane480GenDeadBound0049
  | ⟨50, _⟩ => plane480GenDeadBound0050
  | ⟨51, _⟩ => plane480GenDeadBound0051
  | ⟨52, _⟩ => plane480GenDeadBound0052
  | ⟨53, _⟩ => plane480GenDeadBound0053
  | ⟨54, _⟩ => plane480GenDeadBound0054
  | ⟨55, _⟩ => plane480GenDeadBound0055
  | ⟨56, _⟩ => plane480GenDeadBound0056
  | ⟨57, _⟩ => plane480GenDeadBound0057
  | ⟨58, _⟩ => plane480GenDeadBound0058
  | ⟨59, _⟩ => plane480GenDeadBound0059
  | ⟨60, _⟩ => plane480GenDeadBound0060
  | ⟨61, _⟩ => plane480GenDeadBound0061
  | ⟨62, _⟩ => plane480GenDeadBound0062
  | ⟨63, _⟩ => plane480GenDeadBound0063
  | ⟨64, _⟩ => plane480GenDeadBound0064
  | ⟨65, _⟩ => plane480GenDeadBound0065
  | ⟨66, _⟩ => plane480GenDeadBound0066
  | ⟨67, _⟩ => plane480GenDeadBound0067
  | ⟨68, _⟩ => plane480GenDeadBound0068
  | ⟨69, _⟩ => plane480GenDeadBound0069
  | ⟨70, _⟩ => plane480GenDeadBound0070
  | ⟨71, _⟩ => plane480GenDeadBound0071
  | ⟨72, _⟩ => plane480GenDeadBound0072
  | ⟨73, _⟩ => plane480GenDeadBound0073
  | ⟨74, _⟩ => plane480GenDeadBound0074
  | ⟨75, _⟩ => plane480GenDeadBound0075
  | ⟨76, _⟩ => plane480GenDeadBound0076
  | ⟨77, _⟩ => plane480GenDeadBound0077
  | ⟨78, _⟩ => plane480GenDeadBound0078
  | ⟨79, _⟩ => plane480GenDeadBound0079
  | ⟨80, _⟩ => plane480GenDeadBound0080
  | ⟨81, _⟩ => plane480GenDeadBound0081
  | ⟨82, _⟩ => plane480GenDeadBound0082
  | ⟨83, _⟩ => plane480GenDeadBound0083
  | ⟨84, _⟩ => plane480GenDeadBound0084
  | ⟨85, _⟩ => plane480GenDeadBound0085
  | ⟨86, _⟩ => plane480GenDeadBound0086
  | ⟨87, _⟩ => plane480GenDeadBound0087
  | ⟨88, _⟩ => plane480GenDeadBound0088
  | ⟨89, _⟩ => plane480GenDeadBound0089
  | ⟨90, _⟩ => plane480GenDeadBound0090
  | ⟨91, _⟩ => plane480GenDeadBound0091
  | ⟨92, _⟩ => plane480GenDeadBound0092
  | ⟨93, _⟩ => plane480GenDeadBound0093
  | ⟨94, _⟩ => plane480GenDeadBound0094
  | ⟨95, _⟩ => plane480GenDeadBound0095
  | ⟨96, _⟩ => plane480GenDeadBound0096
  | ⟨97, _⟩ => plane480GenDeadBound0097
  | ⟨98, _⟩ => plane480GenDeadBound0098
  | ⟨99, _⟩ => plane480GenDeadBound0099
  | ⟨100, _⟩ => plane480GenDeadBound0100
  | ⟨k + 101, h⟩ => by omega
end QiushiMatmul
