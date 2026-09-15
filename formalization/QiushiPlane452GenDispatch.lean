import QiushiPlane452GenBindings00
import QiushiPlane452GenBindings01
import QiushiPlane452GenBindings02
import QiushiPlane452GenBindings03
import QiushiPlane452GenBindings04
import QiushiPlane452GenBindings05
import QiushiPlane452GenBindings06
import QiushiPlane452GenBindings07
import QiushiPlane452GenBindings08
import QiushiPlane452GenBindings09
import QiushiPlane452GenBindings10
import QiushiPlane452GenBindings11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane452GenSourceQRA (i : Fin 117) :
    QuotientRankAtLeast (spanCodes (plane452GenSourceBasis i)) (plane452GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane452GenBound0000
  | ⟨1, _⟩ => plane452GenBound0001
  | ⟨2, _⟩ => plane452GenBound0002
  | ⟨3, _⟩ => plane452GenBound0003
  | ⟨4, _⟩ => plane452GenBound0004
  | ⟨5, _⟩ => plane452GenBound0005
  | ⟨6, _⟩ => plane452GenBound0006
  | ⟨7, _⟩ => plane452GenBound0007
  | ⟨8, _⟩ => plane452GenBound0008
  | ⟨9, _⟩ => plane452GenBound0009
  | ⟨10, _⟩ => plane452GenBound0010
  | ⟨11, _⟩ => plane452GenBound0011
  | ⟨12, _⟩ => plane452GenBound0012
  | ⟨13, _⟩ => plane452GenBound0013
  | ⟨14, _⟩ => plane452GenBound0014
  | ⟨15, _⟩ => plane452GenBound0015
  | ⟨16, _⟩ => plane452GenBound0016
  | ⟨17, _⟩ => plane452GenBound0017
  | ⟨18, _⟩ => plane452GenBound0018
  | ⟨19, _⟩ => plane452GenBound0019
  | ⟨20, _⟩ => plane452GenBound0020
  | ⟨21, _⟩ => plane452GenBound0021
  | ⟨22, _⟩ => plane452GenBound0022
  | ⟨23, _⟩ => plane452GenBound0023
  | ⟨24, _⟩ => plane452GenBound0024
  | ⟨25, _⟩ => plane452GenBound0025
  | ⟨26, _⟩ => plane452GenBound0026
  | ⟨27, _⟩ => plane452GenBound0027
  | ⟨28, _⟩ => plane452GenBound0028
  | ⟨29, _⟩ => plane452GenBound0029
  | ⟨30, _⟩ => plane452GenBound0030
  | ⟨31, _⟩ => plane452GenBound0031
  | ⟨32, _⟩ => plane452GenBound0032
  | ⟨33, _⟩ => plane452GenBound0033
  | ⟨34, _⟩ => plane452GenBound0034
  | ⟨35, _⟩ => plane452GenBound0035
  | ⟨36, _⟩ => plane452GenBound0036
  | ⟨37, _⟩ => plane452GenBound0037
  | ⟨38, _⟩ => plane452GenBound0038
  | ⟨39, _⟩ => plane452GenBound0039
  | ⟨40, _⟩ => plane452GenBound0040
  | ⟨41, _⟩ => plane452GenBound0041
  | ⟨42, _⟩ => plane452GenBound0042
  | ⟨43, _⟩ => plane452GenBound0043
  | ⟨44, _⟩ => plane452GenBound0044
  | ⟨45, _⟩ => plane452GenBound0045
  | ⟨46, _⟩ => plane452GenBound0046
  | ⟨47, _⟩ => plane452GenBound0047
  | ⟨48, _⟩ => plane452GenBound0048
  | ⟨49, _⟩ => plane452GenBound0049
  | ⟨50, _⟩ => plane452GenBound0050
  | ⟨51, _⟩ => plane452GenBound0051
  | ⟨52, _⟩ => plane452GenBound0052
  | ⟨53, _⟩ => plane452GenBound0053
  | ⟨54, _⟩ => plane452GenBound0054
  | ⟨55, _⟩ => plane452GenBound0055
  | ⟨56, _⟩ => plane452GenBound0056
  | ⟨57, _⟩ => plane452GenBound0057
  | ⟨58, _⟩ => plane452GenBound0058
  | ⟨59, _⟩ => plane452GenBound0059
  | ⟨60, _⟩ => plane452GenBound0060
  | ⟨61, _⟩ => plane452GenBound0061
  | ⟨62, _⟩ => plane452GenBound0062
  | ⟨63, _⟩ => plane452GenBound0063
  | ⟨64, _⟩ => plane452GenBound0064
  | ⟨65, _⟩ => plane452GenBound0065
  | ⟨66, _⟩ => plane452GenBound0066
  | ⟨67, _⟩ => plane452GenBound0067
  | ⟨68, _⟩ => plane452GenBound0068
  | ⟨69, _⟩ => plane452GenBound0069
  | ⟨70, _⟩ => plane452GenBound0070
  | ⟨71, _⟩ => plane452GenBound0071
  | ⟨72, _⟩ => plane452GenBound0072
  | ⟨73, _⟩ => plane452GenBound0073
  | ⟨74, _⟩ => plane452GenBound0074
  | ⟨75, _⟩ => plane452GenBound0075
  | ⟨76, _⟩ => plane452GenBound0076
  | ⟨77, _⟩ => plane452GenBound0077
  | ⟨78, _⟩ => plane452GenBound0078
  | ⟨79, _⟩ => plane452GenBound0079
  | ⟨80, _⟩ => plane452GenBound0080
  | ⟨81, _⟩ => plane452GenBound0081
  | ⟨82, _⟩ => plane452GenBound0082
  | ⟨83, _⟩ => plane452GenBound0083
  | ⟨84, _⟩ => plane452GenBound0084
  | ⟨85, _⟩ => plane452GenBound0085
  | ⟨86, _⟩ => plane452GenBound0086
  | ⟨87, _⟩ => plane452GenBound0087
  | ⟨88, _⟩ => plane452GenBound0088
  | ⟨89, _⟩ => plane452GenBound0089
  | ⟨90, _⟩ => plane452GenBound0090
  | ⟨91, _⟩ => plane452GenBound0091
  | ⟨92, _⟩ => plane452GenBound0092
  | ⟨93, _⟩ => plane452GenBound0093
  | ⟨94, _⟩ => plane452GenBound0094
  | ⟨95, _⟩ => plane452GenBound0095
  | ⟨96, _⟩ => plane452GenBound0096
  | ⟨97, _⟩ => plane452GenBound0097
  | ⟨98, _⟩ => plane452GenBound0098
  | ⟨99, _⟩ => plane452GenBound0099
  | ⟨100, _⟩ => plane452GenBound0100
  | ⟨101, _⟩ => plane452GenBound0101
  | ⟨102, _⟩ => plane452GenBound0102
  | ⟨103, _⟩ => plane452GenBound0103
  | ⟨104, _⟩ => plane452GenBound0104
  | ⟨105, _⟩ => plane452GenBound0105
  | ⟨106, _⟩ => plane452GenBound0106
  | ⟨107, _⟩ => plane452GenBound0107
  | ⟨108, _⟩ => plane452GenBound0108
  | ⟨109, _⟩ => plane452GenBound0109
  | ⟨110, _⟩ => plane452GenBound0110
  | ⟨111, _⟩ => plane452GenBound0111
  | ⟨112, _⟩ => plane452GenBound0112
  | ⟨113, _⟩ => plane452GenBound0113
  | ⟨114, _⟩ => plane452GenBound0114
  | ⟨115, _⟩ => plane452GenBound0115
  | ⟨116, _⟩ => plane452GenBound0116
  | ⟨k + 117, h⟩ => by omega
theorem plane452GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (0 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (0 : Fin 28) = [68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0000 (by decide)
theorem plane452GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (1 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (1 : Fin 28) = [69, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0001 (by decide)
theorem plane452GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (2 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (2 : Fin 28) = [70, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0002 (by decide)
theorem plane452GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (3 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (3 : Fin 28) = [71, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0003 (by decide)
theorem plane452GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (4 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (4 : Fin 28) = [129, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0004 (by decide)
theorem plane452GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (5 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (5 : Fin 28) = [131, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0005 (by decide)
theorem plane452GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (6 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (6 : Fin 28) = [133, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0006 (by decide)
theorem plane452GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (7 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (7 : Fin 28) = [135, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0007 (by decide)
theorem plane452GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (8 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (8 : Fin 28) = [193, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0008 (by decide)
theorem plane452GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (9 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (9 : Fin 28) = [194, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0009 (by decide)
theorem plane452GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (10 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (10 : Fin 28) = [196, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0010 (by decide)
theorem plane452GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (11 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (11 : Fin 28) = [199, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0011 (by decide)
theorem plane452GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (12 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (12 : Fin 28) = [257, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0012 (by decide)
theorem plane452GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (13 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (13 : Fin 28) = [258, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0013 (by decide)
theorem plane452GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (14 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (14 : Fin 28) = [261, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0014 (by decide)
theorem plane452GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (15 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (15 : Fin 28) = [262, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0015 (by decide)
theorem plane452GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (16 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (16 : Fin 28) = [322, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0016 (by decide)
theorem plane452GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (17 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (17 : Fin 28) = [323, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0017 (by decide)
theorem plane452GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (18 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (18 : Fin 28) = [326, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0018 (by decide)
theorem plane452GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (19 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (19 : Fin 28) = [327, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0019 (by decide)
theorem plane452GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (20 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (20 : Fin 28) = [386, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0020 (by decide)
theorem plane452GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (21 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (21 : Fin 28) = [387, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0021 (by decide)
theorem plane452GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (22 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (22 : Fin 28) = [388, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0022 (by decide)
theorem plane452GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (23 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (23 : Fin 28) = [389, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0023 (by decide)
theorem plane452GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (24 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (24 : Fin 28) = [449, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0024 (by decide)
theorem plane452GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (25 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (25 : Fin 28) = [451, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0025 (by decide)
theorem plane452GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (26 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (26 : Fin 28) = [452, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0026 (by decide)
theorem plane452GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis (27 : Fin 28))) 17 := by
  rw [show plane452GenDeadBasis (27 : Fin 28) = [454, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane452GenSource0027 (by decide)
theorem plane452GenDeadQRA (d : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane452GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane452GenDeadBound0000
  | ⟨1, _⟩ => plane452GenDeadBound0001
  | ⟨2, _⟩ => plane452GenDeadBound0002
  | ⟨3, _⟩ => plane452GenDeadBound0003
  | ⟨4, _⟩ => plane452GenDeadBound0004
  | ⟨5, _⟩ => plane452GenDeadBound0005
  | ⟨6, _⟩ => plane452GenDeadBound0006
  | ⟨7, _⟩ => plane452GenDeadBound0007
  | ⟨8, _⟩ => plane452GenDeadBound0008
  | ⟨9, _⟩ => plane452GenDeadBound0009
  | ⟨10, _⟩ => plane452GenDeadBound0010
  | ⟨11, _⟩ => plane452GenDeadBound0011
  | ⟨12, _⟩ => plane452GenDeadBound0012
  | ⟨13, _⟩ => plane452GenDeadBound0013
  | ⟨14, _⟩ => plane452GenDeadBound0014
  | ⟨15, _⟩ => plane452GenDeadBound0015
  | ⟨16, _⟩ => plane452GenDeadBound0016
  | ⟨17, _⟩ => plane452GenDeadBound0017
  | ⟨18, _⟩ => plane452GenDeadBound0018
  | ⟨19, _⟩ => plane452GenDeadBound0019
  | ⟨20, _⟩ => plane452GenDeadBound0020
  | ⟨21, _⟩ => plane452GenDeadBound0021
  | ⟨22, _⟩ => plane452GenDeadBound0022
  | ⟨23, _⟩ => plane452GenDeadBound0023
  | ⟨24, _⟩ => plane452GenDeadBound0024
  | ⟨25, _⟩ => plane452GenDeadBound0025
  | ⟨26, _⟩ => plane452GenDeadBound0026
  | ⟨27, _⟩ => plane452GenDeadBound0027
  | ⟨k + 28, h⟩ => by omega
end QiushiMatmul
