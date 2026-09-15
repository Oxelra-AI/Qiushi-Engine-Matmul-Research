import QiushiPlane455GenBindings00
import QiushiPlane455GenBindings01
import QiushiPlane455GenBindings02
import QiushiPlane455GenBindings03
import QiushiPlane455GenBindings04
import QiushiPlane455GenBindings05
import QiushiPlane455GenBindings06
import QiushiPlane455GenBindings07
import QiushiPlane455GenBindings08
import QiushiPlane455GenBindings09
import QiushiPlane455GenBindings10
import QiushiPlane455GenBindings11
import QiushiPlane455GenBindings12
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane455GenSourceQRA (i : Fin 124) :
    QuotientRankAtLeast (spanCodes (plane455GenSourceBasis i)) (plane455GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane455GenBound0000
  | ⟨1, _⟩ => plane455GenBound0001
  | ⟨2, _⟩ => plane455GenBound0002
  | ⟨3, _⟩ => plane455GenBound0003
  | ⟨4, _⟩ => plane455GenBound0004
  | ⟨5, _⟩ => plane455GenBound0005
  | ⟨6, _⟩ => plane455GenBound0006
  | ⟨7, _⟩ => plane455GenBound0007
  | ⟨8, _⟩ => plane455GenBound0008
  | ⟨9, _⟩ => plane455GenBound0009
  | ⟨10, _⟩ => plane455GenBound0010
  | ⟨11, _⟩ => plane455GenBound0011
  | ⟨12, _⟩ => plane455GenBound0012
  | ⟨13, _⟩ => plane455GenBound0013
  | ⟨14, _⟩ => plane455GenBound0014
  | ⟨15, _⟩ => plane455GenBound0015
  | ⟨16, _⟩ => plane455GenBound0016
  | ⟨17, _⟩ => plane455GenBound0017
  | ⟨18, _⟩ => plane455GenBound0018
  | ⟨19, _⟩ => plane455GenBound0019
  | ⟨20, _⟩ => plane455GenBound0020
  | ⟨21, _⟩ => plane455GenBound0021
  | ⟨22, _⟩ => plane455GenBound0022
  | ⟨23, _⟩ => plane455GenBound0023
  | ⟨24, _⟩ => plane455GenBound0024
  | ⟨25, _⟩ => plane455GenBound0025
  | ⟨26, _⟩ => plane455GenBound0026
  | ⟨27, _⟩ => plane455GenBound0027
  | ⟨28, _⟩ => plane455GenBound0028
  | ⟨29, _⟩ => plane455GenBound0029
  | ⟨30, _⟩ => plane455GenBound0030
  | ⟨31, _⟩ => plane455GenBound0031
  | ⟨32, _⟩ => plane455GenBound0032
  | ⟨33, _⟩ => plane455GenBound0033
  | ⟨34, _⟩ => plane455GenBound0034
  | ⟨35, _⟩ => plane455GenBound0035
  | ⟨36, _⟩ => plane455GenBound0036
  | ⟨37, _⟩ => plane455GenBound0037
  | ⟨38, _⟩ => plane455GenBound0038
  | ⟨39, _⟩ => plane455GenBound0039
  | ⟨40, _⟩ => plane455GenBound0040
  | ⟨41, _⟩ => plane455GenBound0041
  | ⟨42, _⟩ => plane455GenBound0042
  | ⟨43, _⟩ => plane455GenBound0043
  | ⟨44, _⟩ => plane455GenBound0044
  | ⟨45, _⟩ => plane455GenBound0045
  | ⟨46, _⟩ => plane455GenBound0046
  | ⟨47, _⟩ => plane455GenBound0047
  | ⟨48, _⟩ => plane455GenBound0048
  | ⟨49, _⟩ => plane455GenBound0049
  | ⟨50, _⟩ => plane455GenBound0050
  | ⟨51, _⟩ => plane455GenBound0051
  | ⟨52, _⟩ => plane455GenBound0052
  | ⟨53, _⟩ => plane455GenBound0053
  | ⟨54, _⟩ => plane455GenBound0054
  | ⟨55, _⟩ => plane455GenBound0055
  | ⟨56, _⟩ => plane455GenBound0056
  | ⟨57, _⟩ => plane455GenBound0057
  | ⟨58, _⟩ => plane455GenBound0058
  | ⟨59, _⟩ => plane455GenBound0059
  | ⟨60, _⟩ => plane455GenBound0060
  | ⟨61, _⟩ => plane455GenBound0061
  | ⟨62, _⟩ => plane455GenBound0062
  | ⟨63, _⟩ => plane455GenBound0063
  | ⟨64, _⟩ => plane455GenBound0064
  | ⟨65, _⟩ => plane455GenBound0065
  | ⟨66, _⟩ => plane455GenBound0066
  | ⟨67, _⟩ => plane455GenBound0067
  | ⟨68, _⟩ => plane455GenBound0068
  | ⟨69, _⟩ => plane455GenBound0069
  | ⟨70, _⟩ => plane455GenBound0070
  | ⟨71, _⟩ => plane455GenBound0071
  | ⟨72, _⟩ => plane455GenBound0072
  | ⟨73, _⟩ => plane455GenBound0073
  | ⟨74, _⟩ => plane455GenBound0074
  | ⟨75, _⟩ => plane455GenBound0075
  | ⟨76, _⟩ => plane455GenBound0076
  | ⟨77, _⟩ => plane455GenBound0077
  | ⟨78, _⟩ => plane455GenBound0078
  | ⟨79, _⟩ => plane455GenBound0079
  | ⟨80, _⟩ => plane455GenBound0080
  | ⟨81, _⟩ => plane455GenBound0081
  | ⟨82, _⟩ => plane455GenBound0082
  | ⟨83, _⟩ => plane455GenBound0083
  | ⟨84, _⟩ => plane455GenBound0084
  | ⟨85, _⟩ => plane455GenBound0085
  | ⟨86, _⟩ => plane455GenBound0086
  | ⟨87, _⟩ => plane455GenBound0087
  | ⟨88, _⟩ => plane455GenBound0088
  | ⟨89, _⟩ => plane455GenBound0089
  | ⟨90, _⟩ => plane455GenBound0090
  | ⟨91, _⟩ => plane455GenBound0091
  | ⟨92, _⟩ => plane455GenBound0092
  | ⟨93, _⟩ => plane455GenBound0093
  | ⟨94, _⟩ => plane455GenBound0094
  | ⟨95, _⟩ => plane455GenBound0095
  | ⟨96, _⟩ => plane455GenBound0096
  | ⟨97, _⟩ => plane455GenBound0097
  | ⟨98, _⟩ => plane455GenBound0098
  | ⟨99, _⟩ => plane455GenBound0099
  | ⟨100, _⟩ => plane455GenBound0100
  | ⟨101, _⟩ => plane455GenBound0101
  | ⟨102, _⟩ => plane455GenBound0102
  | ⟨103, _⟩ => plane455GenBound0103
  | ⟨104, _⟩ => plane455GenBound0104
  | ⟨105, _⟩ => plane455GenBound0105
  | ⟨106, _⟩ => plane455GenBound0106
  | ⟨107, _⟩ => plane455GenBound0107
  | ⟨108, _⟩ => plane455GenBound0108
  | ⟨109, _⟩ => plane455GenBound0109
  | ⟨110, _⟩ => plane455GenBound0110
  | ⟨111, _⟩ => plane455GenBound0111
  | ⟨112, _⟩ => plane455GenBound0112
  | ⟨113, _⟩ => plane455GenBound0113
  | ⟨114, _⟩ => plane455GenBound0114
  | ⟨115, _⟩ => plane455GenBound0115
  | ⟨116, _⟩ => plane455GenBound0116
  | ⟨117, _⟩ => plane455GenBound0117
  | ⟨118, _⟩ => plane455GenBound0118
  | ⟨119, _⟩ => plane455GenBound0119
  | ⟨120, _⟩ => plane455GenBound0120
  | ⟨121, _⟩ => plane455GenBound0121
  | ⟨122, _⟩ => plane455GenBound0122
  | ⟨123, _⟩ => plane455GenBound0123
  | ⟨k + 124, h⟩ => by omega
theorem plane455GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (0 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (0 : Fin 15) = [129, 20, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0000 (by decide)
theorem plane455GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (1 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (1 : Fin 15) = [129, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0001 (by decide)
theorem plane455GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (2 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (2 : Fin 15) = [129, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0002 (by decide)
theorem plane455GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (3 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (3 : Fin 15) = [129, 69, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0003 (by decide)
theorem plane455GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (4 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (4 : Fin 15) = [129, 70, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0004 (by decide)
theorem plane455GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (5 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (5 : Fin 15) = [129, 99, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0005 (by decide)
theorem plane455GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (6 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (6 : Fin 15) = [129, 102, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0006 (by decide)
theorem plane455GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (7 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (7 : Fin 15) = [258, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0007 (by decide)
theorem plane455GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (8 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (8 : Fin 15) = [289, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0008 (by decide)
theorem plane455GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (9 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (9 : Fin 15) = [295, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0009 (by decide)
theorem plane455GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (10 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (10 : Fin 15) = [324, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0010 (by decide)
theorem plane455GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (11 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (11 : Fin 15) = [327, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0011 (by decide)
theorem plane455GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (12 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (12 : Fin 15) = [352, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0012 (by decide)
theorem plane455GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (13 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (13 : Fin 15) = [353, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0013 (by decide)
theorem plane455GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis (14 : Fin 15))) 17 := by
  rw [show plane455GenDeadBasis (14 : Fin 15) = [356, 129, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane455GenSource0014 (by decide)
theorem plane455GenDeadQRA (d : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane455GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane455GenDeadBound0000
  | ⟨1, _⟩ => plane455GenDeadBound0001
  | ⟨2, _⟩ => plane455GenDeadBound0002
  | ⟨3, _⟩ => plane455GenDeadBound0003
  | ⟨4, _⟩ => plane455GenDeadBound0004
  | ⟨5, _⟩ => plane455GenDeadBound0005
  | ⟨6, _⟩ => plane455GenDeadBound0006
  | ⟨7, _⟩ => plane455GenDeadBound0007
  | ⟨8, _⟩ => plane455GenDeadBound0008
  | ⟨9, _⟩ => plane455GenDeadBound0009
  | ⟨10, _⟩ => plane455GenDeadBound0010
  | ⟨11, _⟩ => plane455GenDeadBound0011
  | ⟨12, _⟩ => plane455GenDeadBound0012
  | ⟨13, _⟩ => plane455GenDeadBound0013
  | ⟨14, _⟩ => plane455GenDeadBound0014
  | ⟨k + 15, h⟩ => by omega
end QiushiMatmul
