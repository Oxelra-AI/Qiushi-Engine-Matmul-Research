import QiushiPlane482GenBindings00
import QiushiPlane482GenBindings01
import QiushiPlane482GenBindings02
import QiushiPlane482GenBindings03
import QiushiPlane482GenBindings04
import QiushiPlane482GenBindings05
import QiushiPlane482GenBindings06
import QiushiPlane482GenBindings07
import QiushiPlane482GenBindings08
import QiushiPlane482GenBindings09
import QiushiPlane482GenBindings10
import QiushiPlane482GenBindings11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane482GenSourceQRA (i : Fin 118) :
    QuotientRankAtLeast (spanCodes (plane482GenSourceBasis i)) (plane482GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane482GenBound0000
  | ⟨1, _⟩ => plane482GenBound0001
  | ⟨2, _⟩ => plane482GenBound0002
  | ⟨3, _⟩ => plane482GenBound0003
  | ⟨4, _⟩ => plane482GenBound0004
  | ⟨5, _⟩ => plane482GenBound0005
  | ⟨6, _⟩ => plane482GenBound0006
  | ⟨7, _⟩ => plane482GenBound0007
  | ⟨8, _⟩ => plane482GenBound0008
  | ⟨9, _⟩ => plane482GenBound0009
  | ⟨10, _⟩ => plane482GenBound0010
  | ⟨11, _⟩ => plane482GenBound0011
  | ⟨12, _⟩ => plane482GenBound0012
  | ⟨13, _⟩ => plane482GenBound0013
  | ⟨14, _⟩ => plane482GenBound0014
  | ⟨15, _⟩ => plane482GenBound0015
  | ⟨16, _⟩ => plane482GenBound0016
  | ⟨17, _⟩ => plane482GenBound0017
  | ⟨18, _⟩ => plane482GenBound0018
  | ⟨19, _⟩ => plane482GenBound0019
  | ⟨20, _⟩ => plane482GenBound0020
  | ⟨21, _⟩ => plane482GenBound0021
  | ⟨22, _⟩ => plane482GenBound0022
  | ⟨23, _⟩ => plane482GenBound0023
  | ⟨24, _⟩ => plane482GenBound0024
  | ⟨25, _⟩ => plane482GenBound0025
  | ⟨26, _⟩ => plane482GenBound0026
  | ⟨27, _⟩ => plane482GenBound0027
  | ⟨28, _⟩ => plane482GenBound0028
  | ⟨29, _⟩ => plane482GenBound0029
  | ⟨30, _⟩ => plane482GenBound0030
  | ⟨31, _⟩ => plane482GenBound0031
  | ⟨32, _⟩ => plane482GenBound0032
  | ⟨33, _⟩ => plane482GenBound0033
  | ⟨34, _⟩ => plane482GenBound0034
  | ⟨35, _⟩ => plane482GenBound0035
  | ⟨36, _⟩ => plane482GenBound0036
  | ⟨37, _⟩ => plane482GenBound0037
  | ⟨38, _⟩ => plane482GenBound0038
  | ⟨39, _⟩ => plane482GenBound0039
  | ⟨40, _⟩ => plane482GenBound0040
  | ⟨41, _⟩ => plane482GenBound0041
  | ⟨42, _⟩ => plane482GenBound0042
  | ⟨43, _⟩ => plane482GenBound0043
  | ⟨44, _⟩ => plane482GenBound0044
  | ⟨45, _⟩ => plane482GenBound0045
  | ⟨46, _⟩ => plane482GenBound0046
  | ⟨47, _⟩ => plane482GenBound0047
  | ⟨48, _⟩ => plane482GenBound0048
  | ⟨49, _⟩ => plane482GenBound0049
  | ⟨50, _⟩ => plane482GenBound0050
  | ⟨51, _⟩ => plane482GenBound0051
  | ⟨52, _⟩ => plane482GenBound0052
  | ⟨53, _⟩ => plane482GenBound0053
  | ⟨54, _⟩ => plane482GenBound0054
  | ⟨55, _⟩ => plane482GenBound0055
  | ⟨56, _⟩ => plane482GenBound0056
  | ⟨57, _⟩ => plane482GenBound0057
  | ⟨58, _⟩ => plane482GenBound0058
  | ⟨59, _⟩ => plane482GenBound0059
  | ⟨60, _⟩ => plane482GenBound0060
  | ⟨61, _⟩ => plane482GenBound0061
  | ⟨62, _⟩ => plane482GenBound0062
  | ⟨63, _⟩ => plane482GenBound0063
  | ⟨64, _⟩ => plane482GenBound0064
  | ⟨65, _⟩ => plane482GenBound0065
  | ⟨66, _⟩ => plane482GenBound0066
  | ⟨67, _⟩ => plane482GenBound0067
  | ⟨68, _⟩ => plane482GenBound0068
  | ⟨69, _⟩ => plane482GenBound0069
  | ⟨70, _⟩ => plane482GenBound0070
  | ⟨71, _⟩ => plane482GenBound0071
  | ⟨72, _⟩ => plane482GenBound0072
  | ⟨73, _⟩ => plane482GenBound0073
  | ⟨74, _⟩ => plane482GenBound0074
  | ⟨75, _⟩ => plane482GenBound0075
  | ⟨76, _⟩ => plane482GenBound0076
  | ⟨77, _⟩ => plane482GenBound0077
  | ⟨78, _⟩ => plane482GenBound0078
  | ⟨79, _⟩ => plane482GenBound0079
  | ⟨80, _⟩ => plane482GenBound0080
  | ⟨81, _⟩ => plane482GenBound0081
  | ⟨82, _⟩ => plane482GenBound0082
  | ⟨83, _⟩ => plane482GenBound0083
  | ⟨84, _⟩ => plane482GenBound0084
  | ⟨85, _⟩ => plane482GenBound0085
  | ⟨86, _⟩ => plane482GenBound0086
  | ⟨87, _⟩ => plane482GenBound0087
  | ⟨88, _⟩ => plane482GenBound0088
  | ⟨89, _⟩ => plane482GenBound0089
  | ⟨90, _⟩ => plane482GenBound0090
  | ⟨91, _⟩ => plane482GenBound0091
  | ⟨92, _⟩ => plane482GenBound0092
  | ⟨93, _⟩ => plane482GenBound0093
  | ⟨94, _⟩ => plane482GenBound0094
  | ⟨95, _⟩ => plane482GenBound0095
  | ⟨96, _⟩ => plane482GenBound0096
  | ⟨97, _⟩ => plane482GenBound0097
  | ⟨98, _⟩ => plane482GenBound0098
  | ⟨99, _⟩ => plane482GenBound0099
  | ⟨100, _⟩ => plane482GenBound0100
  | ⟨101, _⟩ => plane482GenBound0101
  | ⟨102, _⟩ => plane482GenBound0102
  | ⟨103, _⟩ => plane482GenBound0103
  | ⟨104, _⟩ => plane482GenBound0104
  | ⟨105, _⟩ => plane482GenBound0105
  | ⟨106, _⟩ => plane482GenBound0106
  | ⟨107, _⟩ => plane482GenBound0107
  | ⟨108, _⟩ => plane482GenBound0108
  | ⟨109, _⟩ => plane482GenBound0109
  | ⟨110, _⟩ => plane482GenBound0110
  | ⟨111, _⟩ => plane482GenBound0111
  | ⟨112, _⟩ => plane482GenBound0112
  | ⟨113, _⟩ => plane482GenBound0113
  | ⟨114, _⟩ => plane482GenBound0114
  | ⟨115, _⟩ => plane482GenBound0115
  | ⟨116, _⟩ => plane482GenBound0116
  | ⟨117, _⟩ => plane482GenBound0117
  | ⟨k + 118, h⟩ => by omega
theorem plane482GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (0 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (0 : Fin 74) = [84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0000 (by decide)
theorem plane482GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (1 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (1 : Fin 74) = [80, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0001 (by decide)
theorem plane482GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (2 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (2 : Fin 74) = [82, 6, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0002 (by decide)
theorem plane482GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (3 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (3 : Fin 74) = [84, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0003 (by decide)
theorem plane482GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (4 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (4 : Fin 74) = [84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0004 (by decide)
theorem plane482GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (5 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (5 : Fin 74) = [68, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0005 (by decide)
theorem plane482GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (6 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (6 : Fin 74) = [70, 18, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0006 (by decide)
theorem plane482GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (7 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (7 : Fin 74) = [64, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0007 (by decide)
theorem plane482GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (8 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (8 : Fin 74) = [76, 24, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0008 (by decide)
theorem plane482GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (9 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (9 : Fin 74) = [66, 22, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0009 (by decide)
theorem plane482GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (10 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (10 : Fin 74) = [78, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0010 (by decide)
theorem plane482GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (11 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (11 : Fin 74) = [66, 22, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0011 (by decide)
theorem plane482GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (12 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (12 : Fin 74) = [72, 28, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0012 (by decide)
theorem plane482GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (13 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (13 : Fin 74) = [68, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0013 (by decide)
theorem plane482GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (14 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (14 : Fin 74) = [160, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0014 (by decide)
theorem plane482GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (15 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (15 : Fin 74) = [162, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0015 (by decide)
theorem plane482GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (16 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (16 : Fin 74) = [164, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0016 (by decide)
theorem plane482GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (17 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (17 : Fin 74) = [166, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0017 (by decide)
theorem plane482GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (18 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (18 : Fin 74) = [168, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0018 (by decide)
theorem plane482GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (19 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (19 : Fin 74) = [170, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0019 (by decide)
theorem plane482GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (20 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (20 : Fin 74) = [172, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0020 (by decide)
theorem plane482GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (21 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (21 : Fin 74) = [174, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0021 (by decide)
theorem plane482GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (22 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (22 : Fin 74) = [176, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0022 (by decide)
theorem plane482GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (23 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (23 : Fin 74) = [178, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0023 (by decide)
theorem plane482GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (24 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (24 : Fin 74) = [180, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0024 (by decide)
theorem plane482GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (25 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (25 : Fin 74) = [182, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0025 (by decide)
theorem plane482GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (26 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (26 : Fin 74) = [184, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0026 (by decide)
theorem plane482GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (27 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (27 : Fin 74) = [186, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0027 (by decide)
theorem plane482GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (28 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (28 : Fin 74) = [188, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0028 (by decide)
theorem plane482GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (29 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (29 : Fin 74) = [190, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0029 (by decide)
theorem plane482GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (30 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (30 : Fin 74) = [258, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0030 (by decide)
theorem plane482GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (31 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (31 : Fin 74) = [262, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0031 (by decide)
theorem plane482GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (32 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (32 : Fin 74) = [264, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0032 (by decide)
theorem plane482GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (33 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (33 : Fin 74) = [268, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0033 (by decide)
theorem plane482GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (34 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (34 : Fin 74) = [274, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0034 (by decide)
theorem plane482GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (35 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (35 : Fin 74) = [278, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0035 (by decide)
theorem plane482GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (36 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (36 : Fin 74) = [280, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0036 (by decide)
theorem plane482GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (37 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (37 : Fin 74) = [284, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0037 (by decide)
theorem plane482GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (38 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (38 : Fin 74) = [290, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0038 (by decide)
theorem plane482GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (39 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (39 : Fin 74) = [294, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0039 (by decide)
theorem plane482GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (40 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (40 : Fin 74) = [296, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0040 (by decide)
theorem plane482GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (41 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (41 : Fin 74) = [300, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0041 (by decide)
theorem plane482GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (42 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (42 : Fin 74) = [304, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0042 (by decide)
theorem plane482GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (43 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (43 : Fin 74) = [308, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0043 (by decide)
theorem plane482GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (44 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (44 : Fin 74) = [314, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0044 (by decide)
theorem plane482GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (45 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (45 : Fin 74) = [318, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0045 (by decide)
theorem plane482GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (46 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (46 : Fin 74) = [386, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0046 (by decide)
theorem plane482GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (47 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (47 : Fin 74) = [388, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0047 (by decide)
theorem plane482GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (48 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (48 : Fin 74) = [392, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0048 (by decide)
theorem plane482GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (49 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (49 : Fin 74) = [302, 164, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0049 (by decide)
theorem plane482GenDeadBound0050 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (50 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (50 : Fin 74) = [310, 188, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0050 (by decide)
theorem plane482GenDeadBound0051 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (51 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (51 : Fin 74) = [298, 166, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0051 (by decide)
theorem plane482GenDeadBound0052 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (52 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (52 : Fin 74) = [306, 190, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0052 (by decide)
theorem plane482GenDeadBound0053 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (53 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (53 : Fin 74) = [398, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0053 (by decide)
theorem plane482GenDeadBound0054 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (54 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (54 : Fin 74) = [400, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0054 (by decide)
theorem plane482GenDeadBound0055 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (55 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (55 : Fin 74) = [406, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0055 (by decide)
theorem plane482GenDeadBound0056 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (56 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (56 : Fin 74) = [302, 182, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0056 (by decide)
theorem plane482GenDeadBound0057 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (57 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (57 : Fin 74) = [410, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0057 (by decide)
theorem plane482GenDeadBound0058 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (58 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (58 : Fin 74) = [412, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0058 (by decide)
theorem plane482GenDeadBound0059 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (59 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (59 : Fin 74) = [298, 180, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0059 (by decide)
theorem plane482GenDeadBound0060 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (60 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (60 : Fin 74) = [266, 170, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0060 (by decide)
theorem plane482GenDeadBound0061 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (61 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (61 : Fin 74) = [282, 186, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0061 (by decide)
theorem plane482GenDeadBound0062 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (62 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (62 : Fin 74) = [418, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0062 (by decide)
theorem plane482GenDeadBound0063 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (63 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (63 : Fin 74) = [420, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0063 (by decide)
theorem plane482GenDeadBound0064 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (64 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (64 : Fin 74) = [270, 168, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0064 (by decide)
theorem plane482GenDeadBound0065 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (65 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (65 : Fin 74) = [286, 184, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0065 (by decide)
theorem plane482GenDeadBound0066 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (66 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (66 : Fin 74) = [424, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0066 (by decide)
theorem plane482GenDeadBound0067 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (67 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (67 : Fin 74) = [430, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0067 (by decide)
theorem plane482GenDeadBound0068 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (68 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (68 : Fin 74) = [434, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0068 (by decide)
theorem plane482GenDeadBound0069 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (69 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (69 : Fin 74) = [436, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0069 (by decide)
theorem plane482GenDeadBound0070 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (70 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (70 : Fin 74) = [440, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0070 (by decide)
theorem plane482GenDeadBound0071 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (71 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (71 : Fin 74) = [266, 176, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0071 (by decide)
theorem plane482GenDeadBound0072 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (72 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (72 : Fin 74) = [270, 178, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0072 (by decide)
theorem plane482GenDeadBound0073 :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis (73 : Fin 74))) 17 := by
  rw [show plane482GenDeadBasis (73 : Fin 74) = [446, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane482GenSource0073 (by decide)
theorem plane482GenDeadQRA (d : Fin 74) :
    QuotientRankAtLeast (spanCodes (plane482GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane482GenDeadBound0000
  | ⟨1, _⟩ => plane482GenDeadBound0001
  | ⟨2, _⟩ => plane482GenDeadBound0002
  | ⟨3, _⟩ => plane482GenDeadBound0003
  | ⟨4, _⟩ => plane482GenDeadBound0004
  | ⟨5, _⟩ => plane482GenDeadBound0005
  | ⟨6, _⟩ => plane482GenDeadBound0006
  | ⟨7, _⟩ => plane482GenDeadBound0007
  | ⟨8, _⟩ => plane482GenDeadBound0008
  | ⟨9, _⟩ => plane482GenDeadBound0009
  | ⟨10, _⟩ => plane482GenDeadBound0010
  | ⟨11, _⟩ => plane482GenDeadBound0011
  | ⟨12, _⟩ => plane482GenDeadBound0012
  | ⟨13, _⟩ => plane482GenDeadBound0013
  | ⟨14, _⟩ => plane482GenDeadBound0014
  | ⟨15, _⟩ => plane482GenDeadBound0015
  | ⟨16, _⟩ => plane482GenDeadBound0016
  | ⟨17, _⟩ => plane482GenDeadBound0017
  | ⟨18, _⟩ => plane482GenDeadBound0018
  | ⟨19, _⟩ => plane482GenDeadBound0019
  | ⟨20, _⟩ => plane482GenDeadBound0020
  | ⟨21, _⟩ => plane482GenDeadBound0021
  | ⟨22, _⟩ => plane482GenDeadBound0022
  | ⟨23, _⟩ => plane482GenDeadBound0023
  | ⟨24, _⟩ => plane482GenDeadBound0024
  | ⟨25, _⟩ => plane482GenDeadBound0025
  | ⟨26, _⟩ => plane482GenDeadBound0026
  | ⟨27, _⟩ => plane482GenDeadBound0027
  | ⟨28, _⟩ => plane482GenDeadBound0028
  | ⟨29, _⟩ => plane482GenDeadBound0029
  | ⟨30, _⟩ => plane482GenDeadBound0030
  | ⟨31, _⟩ => plane482GenDeadBound0031
  | ⟨32, _⟩ => plane482GenDeadBound0032
  | ⟨33, _⟩ => plane482GenDeadBound0033
  | ⟨34, _⟩ => plane482GenDeadBound0034
  | ⟨35, _⟩ => plane482GenDeadBound0035
  | ⟨36, _⟩ => plane482GenDeadBound0036
  | ⟨37, _⟩ => plane482GenDeadBound0037
  | ⟨38, _⟩ => plane482GenDeadBound0038
  | ⟨39, _⟩ => plane482GenDeadBound0039
  | ⟨40, _⟩ => plane482GenDeadBound0040
  | ⟨41, _⟩ => plane482GenDeadBound0041
  | ⟨42, _⟩ => plane482GenDeadBound0042
  | ⟨43, _⟩ => plane482GenDeadBound0043
  | ⟨44, _⟩ => plane482GenDeadBound0044
  | ⟨45, _⟩ => plane482GenDeadBound0045
  | ⟨46, _⟩ => plane482GenDeadBound0046
  | ⟨47, _⟩ => plane482GenDeadBound0047
  | ⟨48, _⟩ => plane482GenDeadBound0048
  | ⟨49, _⟩ => plane482GenDeadBound0049
  | ⟨50, _⟩ => plane482GenDeadBound0050
  | ⟨51, _⟩ => plane482GenDeadBound0051
  | ⟨52, _⟩ => plane482GenDeadBound0052
  | ⟨53, _⟩ => plane482GenDeadBound0053
  | ⟨54, _⟩ => plane482GenDeadBound0054
  | ⟨55, _⟩ => plane482GenDeadBound0055
  | ⟨56, _⟩ => plane482GenDeadBound0056
  | ⟨57, _⟩ => plane482GenDeadBound0057
  | ⟨58, _⟩ => plane482GenDeadBound0058
  | ⟨59, _⟩ => plane482GenDeadBound0059
  | ⟨60, _⟩ => plane482GenDeadBound0060
  | ⟨61, _⟩ => plane482GenDeadBound0061
  | ⟨62, _⟩ => plane482GenDeadBound0062
  | ⟨63, _⟩ => plane482GenDeadBound0063
  | ⟨64, _⟩ => plane482GenDeadBound0064
  | ⟨65, _⟩ => plane482GenDeadBound0065
  | ⟨66, _⟩ => plane482GenDeadBound0066
  | ⟨67, _⟩ => plane482GenDeadBound0067
  | ⟨68, _⟩ => plane482GenDeadBound0068
  | ⟨69, _⟩ => plane482GenDeadBound0069
  | ⟨70, _⟩ => plane482GenDeadBound0070
  | ⟨71, _⟩ => plane482GenDeadBound0071
  | ⟨72, _⟩ => plane482GenDeadBound0072
  | ⟨73, _⟩ => plane482GenDeadBound0073
  | ⟨k + 74, h⟩ => by omega
end QiushiMatmul
