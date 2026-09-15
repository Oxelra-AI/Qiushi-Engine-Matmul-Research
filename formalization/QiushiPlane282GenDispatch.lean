import QiushiPlane282GenSources00
import QiushiPlane282GenSources01
import QiushiPlane282GenSources02
import QiushiPlane282GenSources03
import QiushiPlane282GenSources04
import QiushiPlane282GenSources05
import QiushiPlane282GenSources06
import QiushiPlane282GenSources07
import QiushiPlane282GenSources08
import QiushiPlane282GenSources09
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane282GenSourceQRA (i : Fin 100) :
    QuotientRankAtLeast (spanCodes (plane282GenSourceBasis i)) (plane282GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane282GenSource0000
  | ⟨1, _⟩ => plane282GenSource0001
  | ⟨2, _⟩ => plane282GenSource0002
  | ⟨3, _⟩ => plane282GenSource0003
  | ⟨4, _⟩ => plane282GenSource0004
  | ⟨5, _⟩ => plane282GenSource0005
  | ⟨6, _⟩ => plane282GenSource0006
  | ⟨7, _⟩ => plane282GenSource0007
  | ⟨8, _⟩ => plane282GenSource0008
  | ⟨9, _⟩ => plane282GenSource0009
  | ⟨10, _⟩ => plane282GenSource0010
  | ⟨11, _⟩ => plane282GenSource0011
  | ⟨12, _⟩ => plane282GenSource0012
  | ⟨13, _⟩ => plane282GenSource0013
  | ⟨14, _⟩ => plane282GenSource0014
  | ⟨15, _⟩ => plane282GenSource0015
  | ⟨16, _⟩ => plane282GenSource0016
  | ⟨17, _⟩ => plane282GenSource0017
  | ⟨18, _⟩ => plane282GenSource0018
  | ⟨19, _⟩ => plane282GenSource0019
  | ⟨20, _⟩ => plane282GenSource0020
  | ⟨21, _⟩ => plane282GenSource0021
  | ⟨22, _⟩ => plane282GenSource0022
  | ⟨23, _⟩ => plane282GenSource0023
  | ⟨24, _⟩ => plane282GenSource0024
  | ⟨25, _⟩ => plane282GenSource0025
  | ⟨26, _⟩ => plane282GenSource0026
  | ⟨27, _⟩ => plane282GenSource0027
  | ⟨28, _⟩ => plane282GenSource0028
  | ⟨29, _⟩ => plane282GenSource0029
  | ⟨30, _⟩ => plane282GenSource0030
  | ⟨31, _⟩ => plane282GenSource0031
  | ⟨32, _⟩ => plane282GenSource0032
  | ⟨33, _⟩ => plane282GenSource0033
  | ⟨34, _⟩ => plane282GenSource0034
  | ⟨35, _⟩ => plane282GenSource0035
  | ⟨36, _⟩ => plane282GenSource0036
  | ⟨37, _⟩ => plane282GenSource0037
  | ⟨38, _⟩ => plane282GenSource0038
  | ⟨39, _⟩ => plane282GenSource0039
  | ⟨40, _⟩ => plane282GenSource0040
  | ⟨41, _⟩ => plane282GenSource0041
  | ⟨42, _⟩ => plane282GenSource0042
  | ⟨43, _⟩ => plane282GenSource0043
  | ⟨44, _⟩ => plane282GenSource0044
  | ⟨45, _⟩ => plane282GenSource0045
  | ⟨46, _⟩ => plane282GenSource0046
  | ⟨47, _⟩ => plane282GenSource0047
  | ⟨48, _⟩ => plane282GenSource0048
  | ⟨49, _⟩ => plane282GenSource0049
  | ⟨50, _⟩ => plane282GenSource0050
  | ⟨51, _⟩ => plane282GenSource0051
  | ⟨52, _⟩ => plane282GenSource0052
  | ⟨53, _⟩ => plane282GenSource0053
  | ⟨54, _⟩ => plane282GenSource0054
  | ⟨55, _⟩ => plane282GenSource0055
  | ⟨56, _⟩ => plane282GenSource0056
  | ⟨57, _⟩ => plane282GenSource0057
  | ⟨58, _⟩ => plane282GenSource0058
  | ⟨59, _⟩ => plane282GenSource0059
  | ⟨60, _⟩ => plane282GenSource0060
  | ⟨61, _⟩ => plane282GenSource0061
  | ⟨62, _⟩ => plane282GenSource0062
  | ⟨63, _⟩ => plane282GenSource0063
  | ⟨64, _⟩ => plane282GenSource0064
  | ⟨65, _⟩ => plane282GenSource0065
  | ⟨66, _⟩ => plane282GenSource0066
  | ⟨67, _⟩ => plane282GenSource0067
  | ⟨68, _⟩ => plane282GenSource0068
  | ⟨69, _⟩ => plane282GenSource0069
  | ⟨70, _⟩ => plane282GenSource0070
  | ⟨71, _⟩ => plane282GenSource0071
  | ⟨72, _⟩ => plane282GenSource0072
  | ⟨73, _⟩ => plane282GenSource0073
  | ⟨74, _⟩ => plane282GenSource0074
  | ⟨75, _⟩ => plane282GenSource0075
  | ⟨76, _⟩ => plane282GenSource0076
  | ⟨77, _⟩ => plane282GenSource0077
  | ⟨78, _⟩ => plane282GenSource0078
  | ⟨79, _⟩ => plane282GenSource0079
  | ⟨80, _⟩ => plane282GenSource0080
  | ⟨81, _⟩ => plane282GenSource0081
  | ⟨82, _⟩ => plane282GenSource0082
  | ⟨83, _⟩ => plane282GenSource0083
  | ⟨84, _⟩ => plane282GenSource0084
  | ⟨85, _⟩ => plane282GenSource0085
  | ⟨86, _⟩ => plane282GenSource0086
  | ⟨87, _⟩ => plane282GenSource0087
  | ⟨88, _⟩ => plane282GenSource0088
  | ⟨89, _⟩ => plane282GenSource0089
  | ⟨90, _⟩ => plane282GenSource0090
  | ⟨91, _⟩ => plane282GenSource0091
  | ⟨92, _⟩ => plane282GenSource0092
  | ⟨93, _⟩ => plane282GenSource0093
  | ⟨94, _⟩ => plane282GenSource0094
  | ⟨95, _⟩ => plane282GenSource0095
  | ⟨96, _⟩ => plane282GenSource0096
  | ⟨97, _⟩ => plane282GenSource0097
  | ⟨98, _⟩ => plane282GenSource0098
  | ⟨99, _⟩ => plane282GenSource0099
  | ⟨k + 100, h⟩ => by omega

theorem plane282GenDeadQRA (d : Fin 3) :
    QuotientRankAtLeast (spanCodes (plane282GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => quotientRankAtLeast_weaken plane282GenSource0000 (by decide)
  | ⟨1, _⟩ => quotientRankAtLeast_weaken plane282GenSource0001 (by decide)
  | ⟨2, _⟩ => quotientRankAtLeast_weaken plane282GenSource0002 (by decide)

end QiushiMatmul
