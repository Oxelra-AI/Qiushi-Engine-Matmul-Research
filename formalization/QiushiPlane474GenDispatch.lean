import QiushiPlane474GenBindings00
import QiushiPlane474GenBindings01
import QiushiPlane474GenBindings02
import QiushiPlane474GenBindings03
import QiushiPlane474GenBindings04
import QiushiPlane474GenBindings05
import QiushiPlane474GenBindings06
import QiushiPlane474GenBindings07
import QiushiPlane474GenBindings08
import QiushiPlane474GenBindings09
import QiushiPlane474GenBindings10
import QiushiPlane474GenBindings11
import QiushiPlane474GenBindings12
import QiushiPlane474GenBindings13
import QiushiPlane474GenBindings14
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane474GenSourceQRA (i : Fin 146) :
    QuotientRankAtLeast (spanCodes (plane474GenSourceBasis i)) (plane474GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane474GenBound0000
  | ⟨1, _⟩ => plane474GenBound0001
  | ⟨2, _⟩ => plane474GenBound0002
  | ⟨3, _⟩ => plane474GenBound0003
  | ⟨4, _⟩ => plane474GenBound0004
  | ⟨5, _⟩ => plane474GenBound0005
  | ⟨6, _⟩ => plane474GenBound0006
  | ⟨7, _⟩ => plane474GenBound0007
  | ⟨8, _⟩ => plane474GenBound0008
  | ⟨9, _⟩ => plane474GenBound0009
  | ⟨10, _⟩ => plane474GenBound0010
  | ⟨11, _⟩ => plane474GenBound0011
  | ⟨12, _⟩ => plane474GenBound0012
  | ⟨13, _⟩ => plane474GenBound0013
  | ⟨14, _⟩ => plane474GenBound0014
  | ⟨15, _⟩ => plane474GenBound0015
  | ⟨16, _⟩ => plane474GenBound0016
  | ⟨17, _⟩ => plane474GenBound0017
  | ⟨18, _⟩ => plane474GenBound0018
  | ⟨19, _⟩ => plane474GenBound0019
  | ⟨20, _⟩ => plane474GenBound0020
  | ⟨21, _⟩ => plane474GenBound0021
  | ⟨22, _⟩ => plane474GenBound0022
  | ⟨23, _⟩ => plane474GenBound0023
  | ⟨24, _⟩ => plane474GenBound0024
  | ⟨25, _⟩ => plane474GenBound0025
  | ⟨26, _⟩ => plane474GenBound0026
  | ⟨27, _⟩ => plane474GenBound0027
  | ⟨28, _⟩ => plane474GenBound0028
  | ⟨29, _⟩ => plane474GenBound0029
  | ⟨30, _⟩ => plane474GenBound0030
  | ⟨31, _⟩ => plane474GenBound0031
  | ⟨32, _⟩ => plane474GenBound0032
  | ⟨33, _⟩ => plane474GenBound0033
  | ⟨34, _⟩ => plane474GenBound0034
  | ⟨35, _⟩ => plane474GenBound0035
  | ⟨36, _⟩ => plane474GenBound0036
  | ⟨37, _⟩ => plane474GenBound0037
  | ⟨38, _⟩ => plane474GenBound0038
  | ⟨39, _⟩ => plane474GenBound0039
  | ⟨40, _⟩ => plane474GenBound0040
  | ⟨41, _⟩ => plane474GenBound0041
  | ⟨42, _⟩ => plane474GenBound0042
  | ⟨43, _⟩ => plane474GenBound0043
  | ⟨44, _⟩ => plane474GenBound0044
  | ⟨45, _⟩ => plane474GenBound0045
  | ⟨46, _⟩ => plane474GenBound0046
  | ⟨47, _⟩ => plane474GenBound0047
  | ⟨48, _⟩ => plane474GenBound0048
  | ⟨49, _⟩ => plane474GenBound0049
  | ⟨50, _⟩ => plane474GenBound0050
  | ⟨51, _⟩ => plane474GenBound0051
  | ⟨52, _⟩ => plane474GenBound0052
  | ⟨53, _⟩ => plane474GenBound0053
  | ⟨54, _⟩ => plane474GenBound0054
  | ⟨55, _⟩ => plane474GenBound0055
  | ⟨56, _⟩ => plane474GenBound0056
  | ⟨57, _⟩ => plane474GenBound0057
  | ⟨58, _⟩ => plane474GenBound0058
  | ⟨59, _⟩ => plane474GenBound0059
  | ⟨60, _⟩ => plane474GenBound0060
  | ⟨61, _⟩ => plane474GenBound0061
  | ⟨62, _⟩ => plane474GenBound0062
  | ⟨63, _⟩ => plane474GenBound0063
  | ⟨64, _⟩ => plane474GenBound0064
  | ⟨65, _⟩ => plane474GenBound0065
  | ⟨66, _⟩ => plane474GenBound0066
  | ⟨67, _⟩ => plane474GenBound0067
  | ⟨68, _⟩ => plane474GenBound0068
  | ⟨69, _⟩ => plane474GenBound0069
  | ⟨70, _⟩ => plane474GenBound0070
  | ⟨71, _⟩ => plane474GenBound0071
  | ⟨72, _⟩ => plane474GenBound0072
  | ⟨73, _⟩ => plane474GenBound0073
  | ⟨74, _⟩ => plane474GenBound0074
  | ⟨75, _⟩ => plane474GenBound0075
  | ⟨76, _⟩ => plane474GenBound0076
  | ⟨77, _⟩ => plane474GenBound0077
  | ⟨78, _⟩ => plane474GenBound0078
  | ⟨79, _⟩ => plane474GenBound0079
  | ⟨80, _⟩ => plane474GenBound0080
  | ⟨81, _⟩ => plane474GenBound0081
  | ⟨82, _⟩ => plane474GenBound0082
  | ⟨83, _⟩ => plane474GenBound0083
  | ⟨84, _⟩ => plane474GenBound0084
  | ⟨85, _⟩ => plane474GenBound0085
  | ⟨86, _⟩ => plane474GenBound0086
  | ⟨87, _⟩ => plane474GenBound0087
  | ⟨88, _⟩ => plane474GenBound0088
  | ⟨89, _⟩ => plane474GenBound0089
  | ⟨90, _⟩ => plane474GenBound0090
  | ⟨91, _⟩ => plane474GenBound0091
  | ⟨92, _⟩ => plane474GenBound0092
  | ⟨93, _⟩ => plane474GenBound0093
  | ⟨94, _⟩ => plane474GenBound0094
  | ⟨95, _⟩ => plane474GenBound0095
  | ⟨96, _⟩ => plane474GenBound0096
  | ⟨97, _⟩ => plane474GenBound0097
  | ⟨98, _⟩ => plane474GenBound0098
  | ⟨99, _⟩ => plane474GenBound0099
  | ⟨100, _⟩ => plane474GenBound0100
  | ⟨101, _⟩ => plane474GenBound0101
  | ⟨102, _⟩ => plane474GenBound0102
  | ⟨103, _⟩ => plane474GenBound0103
  | ⟨104, _⟩ => plane474GenBound0104
  | ⟨105, _⟩ => plane474GenBound0105
  | ⟨106, _⟩ => plane474GenBound0106
  | ⟨107, _⟩ => plane474GenBound0107
  | ⟨108, _⟩ => plane474GenBound0108
  | ⟨109, _⟩ => plane474GenBound0109
  | ⟨110, _⟩ => plane474GenBound0110
  | ⟨111, _⟩ => plane474GenBound0111
  | ⟨112, _⟩ => plane474GenBound0112
  | ⟨113, _⟩ => plane474GenBound0113
  | ⟨114, _⟩ => plane474GenBound0114
  | ⟨115, _⟩ => plane474GenBound0115
  | ⟨116, _⟩ => plane474GenBound0116
  | ⟨117, _⟩ => plane474GenBound0117
  | ⟨118, _⟩ => plane474GenBound0118
  | ⟨119, _⟩ => plane474GenBound0119
  | ⟨120, _⟩ => plane474GenBound0120
  | ⟨121, _⟩ => plane474GenBound0121
  | ⟨122, _⟩ => plane474GenBound0122
  | ⟨123, _⟩ => plane474GenBound0123
  | ⟨124, _⟩ => plane474GenBound0124
  | ⟨125, _⟩ => plane474GenBound0125
  | ⟨126, _⟩ => plane474GenBound0126
  | ⟨127, _⟩ => plane474GenBound0127
  | ⟨128, _⟩ => plane474GenBound0128
  | ⟨129, _⟩ => plane474GenBound0129
  | ⟨130, _⟩ => plane474GenBound0130
  | ⟨131, _⟩ => plane474GenBound0131
  | ⟨132, _⟩ => plane474GenBound0132
  | ⟨133, _⟩ => plane474GenBound0133
  | ⟨134, _⟩ => plane474GenBound0134
  | ⟨135, _⟩ => plane474GenBound0135
  | ⟨136, _⟩ => plane474GenBound0136
  | ⟨137, _⟩ => plane474GenBound0137
  | ⟨138, _⟩ => plane474GenBound0138
  | ⟨139, _⟩ => plane474GenBound0139
  | ⟨140, _⟩ => plane474GenBound0140
  | ⟨141, _⟩ => plane474GenBound0141
  | ⟨142, _⟩ => plane474GenBound0142
  | ⟨143, _⟩ => plane474GenBound0143
  | ⟨144, _⟩ => plane474GenBound0144
  | ⟨145, _⟩ => plane474GenBound0145
  | ⟨k + 146, h⟩ => by omega
theorem plane474GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane474GenDeadBasis (0 : Fin 3))) 17 := by
  rw [show plane474GenDeadBasis (0 : Fin 3) = [294, 69, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane474GenSource0000 (by decide)
theorem plane474GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane474GenDeadBasis (1 : Fin 3))) 17 := by
  rw [show plane474GenDeadBasis (1 : Fin 3) = [275, 84, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane474GenSource0001 (by decide)
theorem plane474GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane474GenDeadBasis (2 : Fin 3))) 17 := by
  rw [show plane474GenDeadBasis (2 : Fin 3) = [294, 148, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane474GenSource0002 (by decide)
theorem plane474GenDeadQRA (d : Fin 3) :
    QuotientRankAtLeast (spanCodes (plane474GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane474GenDeadBound0000
  | ⟨1, _⟩ => plane474GenDeadBound0001
  | ⟨2, _⟩ => plane474GenDeadBound0002
  | ⟨k + 3, h⟩ => by omega
end QiushiMatmul
