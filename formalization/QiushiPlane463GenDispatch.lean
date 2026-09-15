import QiushiPlane463GenBindings00
import QiushiPlane463GenBindings01
import QiushiPlane463GenBindings02
import QiushiPlane463GenBindings03
import QiushiPlane463GenBindings04
import QiushiPlane463GenBindings05
import QiushiPlane463GenBindings06
import QiushiPlane463GenBindings07
import QiushiPlane463GenBindings08
import QiushiPlane463GenBindings09
import QiushiPlane463GenBindings10
import QiushiPlane463GenBindings11
import QiushiPlane463GenBindings12
import QiushiPlane463GenBindings13
import QiushiPlane463GenBindings14
import QiushiPlane463GenBindings15
import QiushiPlane463GenBindings16
import QiushiPlane463GenBindings17
import QiushiPlane463GenBindings18
import QiushiPlane463GenBindings19
import QiushiPlane463GenBindings20
import QiushiPlane463GenBindings21
import QiushiPlane463GenBindings22
import QiushiPlane463GenBindings23
import QiushiPlane463GenBindings24
import QiushiPlane463GenBindings25
import QiushiPlane463GenBindings26
import QiushiPlane463GenBindings27
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane463GenSourceQRA (i : Fin 278) :
    QuotientRankAtLeast (spanCodes (plane463GenSourceBasis i)) (plane463GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane463GenBound0000
  | ⟨1, _⟩ => plane463GenBound0001
  | ⟨2, _⟩ => plane463GenBound0002
  | ⟨3, _⟩ => plane463GenBound0003
  | ⟨4, _⟩ => plane463GenBound0004
  | ⟨5, _⟩ => plane463GenBound0005
  | ⟨6, _⟩ => plane463GenBound0006
  | ⟨7, _⟩ => plane463GenBound0007
  | ⟨8, _⟩ => plane463GenBound0008
  | ⟨9, _⟩ => plane463GenBound0009
  | ⟨10, _⟩ => plane463GenBound0010
  | ⟨11, _⟩ => plane463GenBound0011
  | ⟨12, _⟩ => plane463GenBound0012
  | ⟨13, _⟩ => plane463GenBound0013
  | ⟨14, _⟩ => plane463GenBound0014
  | ⟨15, _⟩ => plane463GenBound0015
  | ⟨16, _⟩ => plane463GenBound0016
  | ⟨17, _⟩ => plane463GenBound0017
  | ⟨18, _⟩ => plane463GenBound0018
  | ⟨19, _⟩ => plane463GenBound0019
  | ⟨20, _⟩ => plane463GenBound0020
  | ⟨21, _⟩ => plane463GenBound0021
  | ⟨22, _⟩ => plane463GenBound0022
  | ⟨23, _⟩ => plane463GenBound0023
  | ⟨24, _⟩ => plane463GenBound0024
  | ⟨25, _⟩ => plane463GenBound0025
  | ⟨26, _⟩ => plane463GenBound0026
  | ⟨27, _⟩ => plane463GenBound0027
  | ⟨28, _⟩ => plane463GenBound0028
  | ⟨29, _⟩ => plane463GenBound0029
  | ⟨30, _⟩ => plane463GenBound0030
  | ⟨31, _⟩ => plane463GenBound0031
  | ⟨32, _⟩ => plane463GenBound0032
  | ⟨33, _⟩ => plane463GenBound0033
  | ⟨34, _⟩ => plane463GenBound0034
  | ⟨35, _⟩ => plane463GenBound0035
  | ⟨36, _⟩ => plane463GenBound0036
  | ⟨37, _⟩ => plane463GenBound0037
  | ⟨38, _⟩ => plane463GenBound0038
  | ⟨39, _⟩ => plane463GenBound0039
  | ⟨40, _⟩ => plane463GenBound0040
  | ⟨41, _⟩ => plane463GenBound0041
  | ⟨42, _⟩ => plane463GenBound0042
  | ⟨43, _⟩ => plane463GenBound0043
  | ⟨44, _⟩ => plane463GenBound0044
  | ⟨45, _⟩ => plane463GenBound0045
  | ⟨46, _⟩ => plane463GenBound0046
  | ⟨47, _⟩ => plane463GenBound0047
  | ⟨48, _⟩ => plane463GenBound0048
  | ⟨49, _⟩ => plane463GenBound0049
  | ⟨50, _⟩ => plane463GenBound0050
  | ⟨51, _⟩ => plane463GenBound0051
  | ⟨52, _⟩ => plane463GenBound0052
  | ⟨53, _⟩ => plane463GenBound0053
  | ⟨54, _⟩ => plane463GenBound0054
  | ⟨55, _⟩ => plane463GenBound0055
  | ⟨56, _⟩ => plane463GenBound0056
  | ⟨57, _⟩ => plane463GenBound0057
  | ⟨58, _⟩ => plane463GenBound0058
  | ⟨59, _⟩ => plane463GenBound0059
  | ⟨60, _⟩ => plane463GenBound0060
  | ⟨61, _⟩ => plane463GenBound0061
  | ⟨62, _⟩ => plane463GenBound0062
  | ⟨63, _⟩ => plane463GenBound0063
  | ⟨64, _⟩ => plane463GenBound0064
  | ⟨65, _⟩ => plane463GenBound0065
  | ⟨66, _⟩ => plane463GenBound0066
  | ⟨67, _⟩ => plane463GenBound0067
  | ⟨68, _⟩ => plane463GenBound0068
  | ⟨69, _⟩ => plane463GenBound0069
  | ⟨70, _⟩ => plane463GenBound0070
  | ⟨71, _⟩ => plane463GenBound0071
  | ⟨72, _⟩ => plane463GenBound0072
  | ⟨73, _⟩ => plane463GenBound0073
  | ⟨74, _⟩ => plane463GenBound0074
  | ⟨75, _⟩ => plane463GenBound0075
  | ⟨76, _⟩ => plane463GenBound0076
  | ⟨77, _⟩ => plane463GenBound0077
  | ⟨78, _⟩ => plane463GenBound0078
  | ⟨79, _⟩ => plane463GenBound0079
  | ⟨80, _⟩ => plane463GenBound0080
  | ⟨81, _⟩ => plane463GenBound0081
  | ⟨82, _⟩ => plane463GenBound0082
  | ⟨83, _⟩ => plane463GenBound0083
  | ⟨84, _⟩ => plane463GenBound0084
  | ⟨85, _⟩ => plane463GenBound0085
  | ⟨86, _⟩ => plane463GenBound0086
  | ⟨87, _⟩ => plane463GenBound0087
  | ⟨88, _⟩ => plane463GenBound0088
  | ⟨89, _⟩ => plane463GenBound0089
  | ⟨90, _⟩ => plane463GenBound0090
  | ⟨91, _⟩ => plane463GenBound0091
  | ⟨92, _⟩ => plane463GenBound0092
  | ⟨93, _⟩ => plane463GenBound0093
  | ⟨94, _⟩ => plane463GenBound0094
  | ⟨95, _⟩ => plane463GenBound0095
  | ⟨96, _⟩ => plane463GenBound0096
  | ⟨97, _⟩ => plane463GenBound0097
  | ⟨98, _⟩ => plane463GenBound0098
  | ⟨99, _⟩ => plane463GenBound0099
  | ⟨100, _⟩ => plane463GenBound0100
  | ⟨101, _⟩ => plane463GenBound0101
  | ⟨102, _⟩ => plane463GenBound0102
  | ⟨103, _⟩ => plane463GenBound0103
  | ⟨104, _⟩ => plane463GenBound0104
  | ⟨105, _⟩ => plane463GenBound0105
  | ⟨106, _⟩ => plane463GenBound0106
  | ⟨107, _⟩ => plane463GenBound0107
  | ⟨108, _⟩ => plane463GenBound0108
  | ⟨109, _⟩ => plane463GenBound0109
  | ⟨110, _⟩ => plane463GenBound0110
  | ⟨111, _⟩ => plane463GenBound0111
  | ⟨112, _⟩ => plane463GenBound0112
  | ⟨113, _⟩ => plane463GenBound0113
  | ⟨114, _⟩ => plane463GenBound0114
  | ⟨115, _⟩ => plane463GenBound0115
  | ⟨116, _⟩ => plane463GenBound0116
  | ⟨117, _⟩ => plane463GenBound0117
  | ⟨118, _⟩ => plane463GenBound0118
  | ⟨119, _⟩ => plane463GenBound0119
  | ⟨120, _⟩ => plane463GenBound0120
  | ⟨121, _⟩ => plane463GenBound0121
  | ⟨122, _⟩ => plane463GenBound0122
  | ⟨123, _⟩ => plane463GenBound0123
  | ⟨124, _⟩ => plane463GenBound0124
  | ⟨125, _⟩ => plane463GenBound0125
  | ⟨126, _⟩ => plane463GenBound0126
  | ⟨127, _⟩ => plane463GenBound0127
  | ⟨128, _⟩ => plane463GenBound0128
  | ⟨129, _⟩ => plane463GenBound0129
  | ⟨130, _⟩ => plane463GenBound0130
  | ⟨131, _⟩ => plane463GenBound0131
  | ⟨132, _⟩ => plane463GenBound0132
  | ⟨133, _⟩ => plane463GenBound0133
  | ⟨134, _⟩ => plane463GenBound0134
  | ⟨135, _⟩ => plane463GenBound0135
  | ⟨136, _⟩ => plane463GenBound0136
  | ⟨137, _⟩ => plane463GenBound0137
  | ⟨138, _⟩ => plane463GenBound0138
  | ⟨139, _⟩ => plane463GenBound0139
  | ⟨140, _⟩ => plane463GenBound0140
  | ⟨141, _⟩ => plane463GenBound0141
  | ⟨142, _⟩ => plane463GenBound0142
  | ⟨143, _⟩ => plane463GenBound0143
  | ⟨144, _⟩ => plane463GenBound0144
  | ⟨145, _⟩ => plane463GenBound0145
  | ⟨146, _⟩ => plane463GenBound0146
  | ⟨147, _⟩ => plane463GenBound0147
  | ⟨148, _⟩ => plane463GenBound0148
  | ⟨149, _⟩ => plane463GenBound0149
  | ⟨150, _⟩ => plane463GenBound0150
  | ⟨151, _⟩ => plane463GenBound0151
  | ⟨152, _⟩ => plane463GenBound0152
  | ⟨153, _⟩ => plane463GenBound0153
  | ⟨154, _⟩ => plane463GenBound0154
  | ⟨155, _⟩ => plane463GenBound0155
  | ⟨156, _⟩ => plane463GenBound0156
  | ⟨157, _⟩ => plane463GenBound0157
  | ⟨158, _⟩ => plane463GenBound0158
  | ⟨159, _⟩ => plane463GenBound0159
  | ⟨160, _⟩ => plane463GenBound0160
  | ⟨161, _⟩ => plane463GenBound0161
  | ⟨162, _⟩ => plane463GenBound0162
  | ⟨163, _⟩ => plane463GenBound0163
  | ⟨164, _⟩ => plane463GenBound0164
  | ⟨165, _⟩ => plane463GenBound0165
  | ⟨166, _⟩ => plane463GenBound0166
  | ⟨167, _⟩ => plane463GenBound0167
  | ⟨168, _⟩ => plane463GenBound0168
  | ⟨169, _⟩ => plane463GenBound0169
  | ⟨170, _⟩ => plane463GenBound0170
  | ⟨171, _⟩ => plane463GenBound0171
  | ⟨172, _⟩ => plane463GenBound0172
  | ⟨173, _⟩ => plane463GenBound0173
  | ⟨174, _⟩ => plane463GenBound0174
  | ⟨175, _⟩ => plane463GenBound0175
  | ⟨176, _⟩ => plane463GenBound0176
  | ⟨177, _⟩ => plane463GenBound0177
  | ⟨178, _⟩ => plane463GenBound0178
  | ⟨179, _⟩ => plane463GenBound0179
  | ⟨180, _⟩ => plane463GenBound0180
  | ⟨181, _⟩ => plane463GenBound0181
  | ⟨182, _⟩ => plane463GenBound0182
  | ⟨183, _⟩ => plane463GenBound0183
  | ⟨184, _⟩ => plane463GenBound0184
  | ⟨185, _⟩ => plane463GenBound0185
  | ⟨186, _⟩ => plane463GenBound0186
  | ⟨187, _⟩ => plane463GenBound0187
  | ⟨188, _⟩ => plane463GenBound0188
  | ⟨189, _⟩ => plane463GenBound0189
  | ⟨190, _⟩ => plane463GenBound0190
  | ⟨191, _⟩ => plane463GenBound0191
  | ⟨192, _⟩ => plane463GenBound0192
  | ⟨193, _⟩ => plane463GenBound0193
  | ⟨194, _⟩ => plane463GenBound0194
  | ⟨195, _⟩ => plane463GenBound0195
  | ⟨196, _⟩ => plane463GenBound0196
  | ⟨197, _⟩ => plane463GenBound0197
  | ⟨198, _⟩ => plane463GenBound0198
  | ⟨199, _⟩ => plane463GenBound0199
  | ⟨200, _⟩ => plane463GenBound0200
  | ⟨201, _⟩ => plane463GenBound0201
  | ⟨202, _⟩ => plane463GenBound0202
  | ⟨203, _⟩ => plane463GenBound0203
  | ⟨204, _⟩ => plane463GenBound0204
  | ⟨205, _⟩ => plane463GenBound0205
  | ⟨206, _⟩ => plane463GenBound0206
  | ⟨207, _⟩ => plane463GenBound0207
  | ⟨208, _⟩ => plane463GenBound0208
  | ⟨209, _⟩ => plane463GenBound0209
  | ⟨210, _⟩ => plane463GenBound0210
  | ⟨211, _⟩ => plane463GenBound0211
  | ⟨212, _⟩ => plane463GenBound0212
  | ⟨213, _⟩ => plane463GenBound0213
  | ⟨214, _⟩ => plane463GenBound0214
  | ⟨215, _⟩ => plane463GenBound0215
  | ⟨216, _⟩ => plane463GenBound0216
  | ⟨217, _⟩ => plane463GenBound0217
  | ⟨218, _⟩ => plane463GenBound0218
  | ⟨219, _⟩ => plane463GenBound0219
  | ⟨220, _⟩ => plane463GenBound0220
  | ⟨221, _⟩ => plane463GenBound0221
  | ⟨222, _⟩ => plane463GenBound0222
  | ⟨223, _⟩ => plane463GenBound0223
  | ⟨224, _⟩ => plane463GenBound0224
  | ⟨225, _⟩ => plane463GenBound0225
  | ⟨226, _⟩ => plane463GenBound0226
  | ⟨227, _⟩ => plane463GenBound0227
  | ⟨228, _⟩ => plane463GenBound0228
  | ⟨229, _⟩ => plane463GenBound0229
  | ⟨230, _⟩ => plane463GenBound0230
  | ⟨231, _⟩ => plane463GenBound0231
  | ⟨232, _⟩ => plane463GenBound0232
  | ⟨233, _⟩ => plane463GenBound0233
  | ⟨234, _⟩ => plane463GenBound0234
  | ⟨235, _⟩ => plane463GenBound0235
  | ⟨236, _⟩ => plane463GenBound0236
  | ⟨237, _⟩ => plane463GenBound0237
  | ⟨238, _⟩ => plane463GenBound0238
  | ⟨239, _⟩ => plane463GenBound0239
  | ⟨240, _⟩ => plane463GenBound0240
  | ⟨241, _⟩ => plane463GenBound0241
  | ⟨242, _⟩ => plane463GenBound0242
  | ⟨243, _⟩ => plane463GenBound0243
  | ⟨244, _⟩ => plane463GenBound0244
  | ⟨245, _⟩ => plane463GenBound0245
  | ⟨246, _⟩ => plane463GenBound0246
  | ⟨247, _⟩ => plane463GenBound0247
  | ⟨248, _⟩ => plane463GenBound0248
  | ⟨249, _⟩ => plane463GenBound0249
  | ⟨250, _⟩ => plane463GenBound0250
  | ⟨251, _⟩ => plane463GenBound0251
  | ⟨252, _⟩ => plane463GenBound0252
  | ⟨253, _⟩ => plane463GenBound0253
  | ⟨254, _⟩ => plane463GenBound0254
  | ⟨255, _⟩ => plane463GenBound0255
  | ⟨256, _⟩ => plane463GenBound0256
  | ⟨257, _⟩ => plane463GenBound0257
  | ⟨258, _⟩ => plane463GenBound0258
  | ⟨259, _⟩ => plane463GenBound0259
  | ⟨260, _⟩ => plane463GenBound0260
  | ⟨261, _⟩ => plane463GenBound0261
  | ⟨262, _⟩ => plane463GenBound0262
  | ⟨263, _⟩ => plane463GenBound0263
  | ⟨264, _⟩ => plane463GenBound0264
  | ⟨265, _⟩ => plane463GenBound0265
  | ⟨266, _⟩ => plane463GenBound0266
  | ⟨267, _⟩ => plane463GenBound0267
  | ⟨268, _⟩ => plane463GenBound0268
  | ⟨269, _⟩ => plane463GenBound0269
  | ⟨270, _⟩ => plane463GenBound0270
  | ⟨271, _⟩ => plane463GenBound0271
  | ⟨272, _⟩ => plane463GenBound0272
  | ⟨273, _⟩ => plane463GenBound0273
  | ⟨274, _⟩ => plane463GenBound0274
  | ⟨275, _⟩ => plane463GenBound0275
  | ⟨276, _⟩ => plane463GenBound0276
  | ⟨277, _⟩ => plane463GenBound0277
  | ⟨k + 278, h⟩ => by omega
theorem plane463GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane463GenDeadBasis (0 : Fin 1))) 17 := by
  rw [show plane463GenDeadBasis (0 : Fin 1) = [179, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463GenSource0277 (by decide)
theorem plane463GenDeadQRA (d : Fin 1) :
    QuotientRankAtLeast (spanCodes (plane463GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane463GenDeadBound0000
  | ⟨k + 1, h⟩ => by omega
end QiushiMatmul
