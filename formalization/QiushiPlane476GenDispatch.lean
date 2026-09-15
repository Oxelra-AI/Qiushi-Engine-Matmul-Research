import QiushiPlane476GenBindings00
import QiushiPlane476GenBindings01
import QiushiPlane476GenBindings02
import QiushiPlane476GenBindings03
import QiushiPlane476GenBindings04
import QiushiPlane476GenBindings05
import QiushiPlane476GenBindings06
import QiushiPlane476GenBindings07
import QiushiPlane476GenBindings08
import QiushiPlane476GenBindings09
import QiushiPlane476GenBindings10
import QiushiPlane476GenBindings11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane476GenSourceQRA (i : Fin 113) :
    QuotientRankAtLeast (spanCodes (plane476GenSourceBasis i)) (plane476GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane476GenBound0000
  | ⟨1, _⟩ => plane476GenBound0001
  | ⟨2, _⟩ => plane476GenBound0002
  | ⟨3, _⟩ => plane476GenBound0003
  | ⟨4, _⟩ => plane476GenBound0004
  | ⟨5, _⟩ => plane476GenBound0005
  | ⟨6, _⟩ => plane476GenBound0006
  | ⟨7, _⟩ => plane476GenBound0007
  | ⟨8, _⟩ => plane476GenBound0008
  | ⟨9, _⟩ => plane476GenBound0009
  | ⟨10, _⟩ => plane476GenBound0010
  | ⟨11, _⟩ => plane476GenBound0011
  | ⟨12, _⟩ => plane476GenBound0012
  | ⟨13, _⟩ => plane476GenBound0013
  | ⟨14, _⟩ => plane476GenBound0014
  | ⟨15, _⟩ => plane476GenBound0015
  | ⟨16, _⟩ => plane476GenBound0016
  | ⟨17, _⟩ => plane476GenBound0017
  | ⟨18, _⟩ => plane476GenBound0018
  | ⟨19, _⟩ => plane476GenBound0019
  | ⟨20, _⟩ => plane476GenBound0020
  | ⟨21, _⟩ => plane476GenBound0021
  | ⟨22, _⟩ => plane476GenBound0022
  | ⟨23, _⟩ => plane476GenBound0023
  | ⟨24, _⟩ => plane476GenBound0024
  | ⟨25, _⟩ => plane476GenBound0025
  | ⟨26, _⟩ => plane476GenBound0026
  | ⟨27, _⟩ => plane476GenBound0027
  | ⟨28, _⟩ => plane476GenBound0028
  | ⟨29, _⟩ => plane476GenBound0029
  | ⟨30, _⟩ => plane476GenBound0030
  | ⟨31, _⟩ => plane476GenBound0031
  | ⟨32, _⟩ => plane476GenBound0032
  | ⟨33, _⟩ => plane476GenBound0033
  | ⟨34, _⟩ => plane476GenBound0034
  | ⟨35, _⟩ => plane476GenBound0035
  | ⟨36, _⟩ => plane476GenBound0036
  | ⟨37, _⟩ => plane476GenBound0037
  | ⟨38, _⟩ => plane476GenBound0038
  | ⟨39, _⟩ => plane476GenBound0039
  | ⟨40, _⟩ => plane476GenBound0040
  | ⟨41, _⟩ => plane476GenBound0041
  | ⟨42, _⟩ => plane476GenBound0042
  | ⟨43, _⟩ => plane476GenBound0043
  | ⟨44, _⟩ => plane476GenBound0044
  | ⟨45, _⟩ => plane476GenBound0045
  | ⟨46, _⟩ => plane476GenBound0046
  | ⟨47, _⟩ => plane476GenBound0047
  | ⟨48, _⟩ => plane476GenBound0048
  | ⟨49, _⟩ => plane476GenBound0049
  | ⟨50, _⟩ => plane476GenBound0050
  | ⟨51, _⟩ => plane476GenBound0051
  | ⟨52, _⟩ => plane476GenBound0052
  | ⟨53, _⟩ => plane476GenBound0053
  | ⟨54, _⟩ => plane476GenBound0054
  | ⟨55, _⟩ => plane476GenBound0055
  | ⟨56, _⟩ => plane476GenBound0056
  | ⟨57, _⟩ => plane476GenBound0057
  | ⟨58, _⟩ => plane476GenBound0058
  | ⟨59, _⟩ => plane476GenBound0059
  | ⟨60, _⟩ => plane476GenBound0060
  | ⟨61, _⟩ => plane476GenBound0061
  | ⟨62, _⟩ => plane476GenBound0062
  | ⟨63, _⟩ => plane476GenBound0063
  | ⟨64, _⟩ => plane476GenBound0064
  | ⟨65, _⟩ => plane476GenBound0065
  | ⟨66, _⟩ => plane476GenBound0066
  | ⟨67, _⟩ => plane476GenBound0067
  | ⟨68, _⟩ => plane476GenBound0068
  | ⟨69, _⟩ => plane476GenBound0069
  | ⟨70, _⟩ => plane476GenBound0070
  | ⟨71, _⟩ => plane476GenBound0071
  | ⟨72, _⟩ => plane476GenBound0072
  | ⟨73, _⟩ => plane476GenBound0073
  | ⟨74, _⟩ => plane476GenBound0074
  | ⟨75, _⟩ => plane476GenBound0075
  | ⟨76, _⟩ => plane476GenBound0076
  | ⟨77, _⟩ => plane476GenBound0077
  | ⟨78, _⟩ => plane476GenBound0078
  | ⟨79, _⟩ => plane476GenBound0079
  | ⟨80, _⟩ => plane476GenBound0080
  | ⟨81, _⟩ => plane476GenBound0081
  | ⟨82, _⟩ => plane476GenBound0082
  | ⟨83, _⟩ => plane476GenBound0083
  | ⟨84, _⟩ => plane476GenBound0084
  | ⟨85, _⟩ => plane476GenBound0085
  | ⟨86, _⟩ => plane476GenBound0086
  | ⟨87, _⟩ => plane476GenBound0087
  | ⟨88, _⟩ => plane476GenBound0088
  | ⟨89, _⟩ => plane476GenBound0089
  | ⟨90, _⟩ => plane476GenBound0090
  | ⟨91, _⟩ => plane476GenBound0091
  | ⟨92, _⟩ => plane476GenBound0092
  | ⟨93, _⟩ => plane476GenBound0093
  | ⟨94, _⟩ => plane476GenBound0094
  | ⟨95, _⟩ => plane476GenBound0095
  | ⟨96, _⟩ => plane476GenBound0096
  | ⟨97, _⟩ => plane476GenBound0097
  | ⟨98, _⟩ => plane476GenBound0098
  | ⟨99, _⟩ => plane476GenBound0099
  | ⟨100, _⟩ => plane476GenBound0100
  | ⟨101, _⟩ => plane476GenBound0101
  | ⟨102, _⟩ => plane476GenBound0102
  | ⟨103, _⟩ => plane476GenBound0103
  | ⟨104, _⟩ => plane476GenBound0104
  | ⟨105, _⟩ => plane476GenBound0105
  | ⟨106, _⟩ => plane476GenBound0106
  | ⟨107, _⟩ => plane476GenBound0107
  | ⟨108, _⟩ => plane476GenBound0108
  | ⟨109, _⟩ => plane476GenBound0109
  | ⟨110, _⟩ => plane476GenBound0110
  | ⟨111, _⟩ => plane476GenBound0111
  | ⟨112, _⟩ => plane476GenBound0112
  | ⟨k + 113, h⟩ => by omega
theorem plane476GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (0 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (0 : Fin 13) = [261, 96, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0000 (by decide)
theorem plane476GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (1 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (1 : Fin 13) = [263, 96, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0001 (by decide)
theorem plane476GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (2 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (2 : Fin 13) = [257, 96, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0002 (by decide)
theorem plane476GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (3 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (3 : Fin 13) = [258, 96, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0003 (by decide)
theorem plane476GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (4 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (4 : Fin 13) = [276, 70, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0004 (by decide)
theorem plane476GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (5 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (5 : Fin 13) = [276, 83, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0005 (by decide)
theorem plane476GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (6 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (6 : Fin 13) = [276, 86, 54, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0006 (by decide)
theorem plane476GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (7 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (7 : Fin 13) = [276, 131, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0007 (by decide)
theorem plane476GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (8 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (8 : Fin 13) = [276, 150, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0008 (by decide)
theorem plane476GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (9 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (9 : Fin 13) = [276, 162, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0009 (by decide)
theorem plane476GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (10 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (10 : Fin 13) = [276, 165, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0010 (by decide)
theorem plane476GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (11 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (11 : Fin 13) = [276, 176, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0011 (by decide)
theorem plane476GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis (12 : Fin 13))) 17 := by
  rw [show plane476GenDeadBasis (12 : Fin 13) = [276, 178, 96, 10] from rfl]
  exact quotientRankAtLeast_weaken plane476GenSource0012 (by decide)
theorem plane476GenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane476GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane476GenDeadBound0000
  | ⟨1, _⟩ => plane476GenDeadBound0001
  | ⟨2, _⟩ => plane476GenDeadBound0002
  | ⟨3, _⟩ => plane476GenDeadBound0003
  | ⟨4, _⟩ => plane476GenDeadBound0004
  | ⟨5, _⟩ => plane476GenDeadBound0005
  | ⟨6, _⟩ => plane476GenDeadBound0006
  | ⟨7, _⟩ => plane476GenDeadBound0007
  | ⟨8, _⟩ => plane476GenDeadBound0008
  | ⟨9, _⟩ => plane476GenDeadBound0009
  | ⟨10, _⟩ => plane476GenDeadBound0010
  | ⟨11, _⟩ => plane476GenDeadBound0011
  | ⟨12, _⟩ => plane476GenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
