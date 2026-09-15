import QiushiPlane481GenBindings00
import QiushiPlane481GenBindings01
import QiushiPlane481GenBindings02
import QiushiPlane481GenBindings03
import QiushiPlane481GenBindings04
import QiushiPlane481GenBindings05
import QiushiPlane481GenBindings06
import QiushiPlane481GenBindings07
import QiushiPlane481GenBindings08
import QiushiPlane481GenBindings09
import QiushiPlane481GenBindings10
import QiushiPlane481GenBindings11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane481GenSourceQRA (i : Fin 116) :
    QuotientRankAtLeast (spanCodes (plane481GenSourceBasis i)) (plane481GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane481GenBound0000
  | ⟨1, _⟩ => plane481GenBound0001
  | ⟨2, _⟩ => plane481GenBound0002
  | ⟨3, _⟩ => plane481GenBound0003
  | ⟨4, _⟩ => plane481GenBound0004
  | ⟨5, _⟩ => plane481GenBound0005
  | ⟨6, _⟩ => plane481GenBound0006
  | ⟨7, _⟩ => plane481GenBound0007
  | ⟨8, _⟩ => plane481GenBound0008
  | ⟨9, _⟩ => plane481GenBound0009
  | ⟨10, _⟩ => plane481GenBound0010
  | ⟨11, _⟩ => plane481GenBound0011
  | ⟨12, _⟩ => plane481GenBound0012
  | ⟨13, _⟩ => plane481GenBound0013
  | ⟨14, _⟩ => plane481GenBound0014
  | ⟨15, _⟩ => plane481GenBound0015
  | ⟨16, _⟩ => plane481GenBound0016
  | ⟨17, _⟩ => plane481GenBound0017
  | ⟨18, _⟩ => plane481GenBound0018
  | ⟨19, _⟩ => plane481GenBound0019
  | ⟨20, _⟩ => plane481GenBound0020
  | ⟨21, _⟩ => plane481GenBound0021
  | ⟨22, _⟩ => plane481GenBound0022
  | ⟨23, _⟩ => plane481GenBound0023
  | ⟨24, _⟩ => plane481GenBound0024
  | ⟨25, _⟩ => plane481GenBound0025
  | ⟨26, _⟩ => plane481GenBound0026
  | ⟨27, _⟩ => plane481GenBound0027
  | ⟨28, _⟩ => plane481GenBound0028
  | ⟨29, _⟩ => plane481GenBound0029
  | ⟨30, _⟩ => plane481GenBound0030
  | ⟨31, _⟩ => plane481GenBound0031
  | ⟨32, _⟩ => plane481GenBound0032
  | ⟨33, _⟩ => plane481GenBound0033
  | ⟨34, _⟩ => plane481GenBound0034
  | ⟨35, _⟩ => plane481GenBound0035
  | ⟨36, _⟩ => plane481GenBound0036
  | ⟨37, _⟩ => plane481GenBound0037
  | ⟨38, _⟩ => plane481GenBound0038
  | ⟨39, _⟩ => plane481GenBound0039
  | ⟨40, _⟩ => plane481GenBound0040
  | ⟨41, _⟩ => plane481GenBound0041
  | ⟨42, _⟩ => plane481GenBound0042
  | ⟨43, _⟩ => plane481GenBound0043
  | ⟨44, _⟩ => plane481GenBound0044
  | ⟨45, _⟩ => plane481GenBound0045
  | ⟨46, _⟩ => plane481GenBound0046
  | ⟨47, _⟩ => plane481GenBound0047
  | ⟨48, _⟩ => plane481GenBound0048
  | ⟨49, _⟩ => plane481GenBound0049
  | ⟨50, _⟩ => plane481GenBound0050
  | ⟨51, _⟩ => plane481GenBound0051
  | ⟨52, _⟩ => plane481GenBound0052
  | ⟨53, _⟩ => plane481GenBound0053
  | ⟨54, _⟩ => plane481GenBound0054
  | ⟨55, _⟩ => plane481GenBound0055
  | ⟨56, _⟩ => plane481GenBound0056
  | ⟨57, _⟩ => plane481GenBound0057
  | ⟨58, _⟩ => plane481GenBound0058
  | ⟨59, _⟩ => plane481GenBound0059
  | ⟨60, _⟩ => plane481GenBound0060
  | ⟨61, _⟩ => plane481GenBound0061
  | ⟨62, _⟩ => plane481GenBound0062
  | ⟨63, _⟩ => plane481GenBound0063
  | ⟨64, _⟩ => plane481GenBound0064
  | ⟨65, _⟩ => plane481GenBound0065
  | ⟨66, _⟩ => plane481GenBound0066
  | ⟨67, _⟩ => plane481GenBound0067
  | ⟨68, _⟩ => plane481GenBound0068
  | ⟨69, _⟩ => plane481GenBound0069
  | ⟨70, _⟩ => plane481GenBound0070
  | ⟨71, _⟩ => plane481GenBound0071
  | ⟨72, _⟩ => plane481GenBound0072
  | ⟨73, _⟩ => plane481GenBound0073
  | ⟨74, _⟩ => plane481GenBound0074
  | ⟨75, _⟩ => plane481GenBound0075
  | ⟨76, _⟩ => plane481GenBound0076
  | ⟨77, _⟩ => plane481GenBound0077
  | ⟨78, _⟩ => plane481GenBound0078
  | ⟨79, _⟩ => plane481GenBound0079
  | ⟨80, _⟩ => plane481GenBound0080
  | ⟨81, _⟩ => plane481GenBound0081
  | ⟨82, _⟩ => plane481GenBound0082
  | ⟨83, _⟩ => plane481GenBound0083
  | ⟨84, _⟩ => plane481GenBound0084
  | ⟨85, _⟩ => plane481GenBound0085
  | ⟨86, _⟩ => plane481GenBound0086
  | ⟨87, _⟩ => plane481GenBound0087
  | ⟨88, _⟩ => plane481GenBound0088
  | ⟨89, _⟩ => plane481GenBound0089
  | ⟨90, _⟩ => plane481GenBound0090
  | ⟨91, _⟩ => plane481GenBound0091
  | ⟨92, _⟩ => plane481GenBound0092
  | ⟨93, _⟩ => plane481GenBound0093
  | ⟨94, _⟩ => plane481GenBound0094
  | ⟨95, _⟩ => plane481GenBound0095
  | ⟨96, _⟩ => plane481GenBound0096
  | ⟨97, _⟩ => plane481GenBound0097
  | ⟨98, _⟩ => plane481GenBound0098
  | ⟨99, _⟩ => plane481GenBound0099
  | ⟨100, _⟩ => plane481GenBound0100
  | ⟨101, _⟩ => plane481GenBound0101
  | ⟨102, _⟩ => plane481GenBound0102
  | ⟨103, _⟩ => plane481GenBound0103
  | ⟨104, _⟩ => plane481GenBound0104
  | ⟨105, _⟩ => plane481GenBound0105
  | ⟨106, _⟩ => plane481GenBound0106
  | ⟨107, _⟩ => plane481GenBound0107
  | ⟨108, _⟩ => plane481GenBound0108
  | ⟨109, _⟩ => plane481GenBound0109
  | ⟨110, _⟩ => plane481GenBound0110
  | ⟨111, _⟩ => plane481GenBound0111
  | ⟨112, _⟩ => plane481GenBound0112
  | ⟨113, _⟩ => plane481GenBound0113
  | ⟨114, _⟩ => plane481GenBound0114
  | ⟨115, _⟩ => plane481GenBound0115
  | ⟨k + 116, h⟩ => by omega
theorem plane481GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (0 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (0 : Fin 69) = [20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0000 (by decide)
theorem plane481GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (1 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (1 : Fin 69) = [20, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0001 (by decide)
theorem plane481GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (2 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (2 : Fin 69) = [38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0002 (by decide)
theorem plane481GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (3 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (3 : Fin 69) = [46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0003 (by decide)
theorem plane481GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (4 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (4 : Fin 69) = [64, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0004 (by decide)
theorem plane481GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (5 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (5 : Fin 69) = [68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0005 (by decide)
theorem plane481GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (6 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (6 : Fin 69) = [72, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0006 (by decide)
theorem plane481GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (7 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (7 : Fin 69) = [68, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0007 (by decide)
theorem plane481GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (8 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (8 : Fin 69) = [70, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0008 (by decide)
theorem plane481GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (9 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (9 : Fin 69) = [66, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0009 (by decide)
theorem plane481GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (10 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (10 : Fin 69) = [66, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0010 (by decide)
theorem plane481GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (11 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (11 : Fin 69) = [100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0011 (by decide)
theorem plane481GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (12 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (12 : Fin 69) = [108, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0012 (by decide)
theorem plane481GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (13 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (13 : Fin 69) = [196, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0013 (by decide)
theorem plane481GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (14 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (14 : Fin 69) = [198, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0014 (by decide)
theorem plane481GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (15 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (15 : Fin 69) = [200, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0015 (by decide)
theorem plane481GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (16 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (16 : Fin 69) = [202, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0016 (by decide)
theorem plane481GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (17 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (17 : Fin 69) = [224, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0017 (by decide)
theorem plane481GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (18 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (18 : Fin 69) = [226, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0018 (by decide)
theorem plane481GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (19 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (19 : Fin 69) = [228, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0019 (by decide)
theorem plane481GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (20 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (20 : Fin 69) = [230, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0020 (by decide)
theorem plane481GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (21 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (21 : Fin 69) = [232, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0021 (by decide)
theorem plane481GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (22 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (22 : Fin 69) = [234, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0022 (by decide)
theorem plane481GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (23 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (23 : Fin 69) = [236, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0023 (by decide)
theorem plane481GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (24 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (24 : Fin 69) = [238, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0024 (by decide)
theorem plane481GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (25 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (25 : Fin 69) = [264, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0025 (by decide)
theorem plane481GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (26 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (26 : Fin 69) = [266, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0026 (by decide)
theorem plane481GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (27 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (27 : Fin 69) = [268, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0027 (by decide)
theorem plane481GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (28 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (28 : Fin 69) = [270, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0028 (by decide)
theorem plane481GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (29 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (29 : Fin 69) = [296, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0029 (by decide)
theorem plane481GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (30 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (30 : Fin 69) = [264, 32, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0030 (by decide)
theorem plane481GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (31 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (31 : Fin 69) = [298, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0031 (by decide)
theorem plane481GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (32 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (32 : Fin 69) = [300, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0032 (by decide)
theorem plane481GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (33 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (33 : Fin 69) = [302, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0033 (by decide)
theorem plane481GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (34 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (34 : Fin 69) = [260, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0034 (by decide)
theorem plane481GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (35 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (35 : Fin 69) = [256, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0035 (by decide)
theorem plane481GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (36 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (36 : Fin 69) = [328, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0036 (by decide)
theorem plane481GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (37 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (37 : Fin 69) = [330, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0037 (by decide)
theorem plane481GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (38 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (38 : Fin 69) = [332, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0038 (by decide)
theorem plane481GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (39 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (39 : Fin 69) = [334, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0039 (by decide)
theorem plane481GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (40 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (40 : Fin 69) = [352, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0040 (by decide)
theorem plane481GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (41 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (41 : Fin 69) = [328, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0041 (by decide)
theorem plane481GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (42 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (42 : Fin 69) = [354, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0042 (by decide)
theorem plane481GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (43 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (43 : Fin 69) = [356, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0043 (by decide)
theorem plane481GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (44 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (44 : Fin 69) = [358, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0044 (by decide)
theorem plane481GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (45 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (45 : Fin 69) = [292, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0045 (by decide)
theorem plane481GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (46 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (46 : Fin 69) = [288, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0046 (by decide)
theorem plane481GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (47 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (47 : Fin 69) = [392, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0047 (by decide)
theorem plane481GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (48 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (48 : Fin 69) = [394, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0048 (by decide)
theorem plane481GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (49 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (49 : Fin 69) = [396, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0049 (by decide)
theorem plane481GenDeadBound0050 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (50 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (50 : Fin 69) = [398, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0050 (by decide)
theorem plane481GenDeadBound0051 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (51 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (51 : Fin 69) = [424, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0051 (by decide)
theorem plane481GenDeadBound0052 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (52 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (52 : Fin 69) = [426, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0052 (by decide)
theorem plane481GenDeadBound0053 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (53 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (53 : Fin 69) = [392, 34, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0053 (by decide)
theorem plane481GenDeadBound0054 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (54 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (54 : Fin 69) = [428, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0054 (by decide)
theorem plane481GenDeadBound0055 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (55 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (55 : Fin 69) = [430, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0055 (by decide)
theorem plane481GenDeadBound0056 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (56 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (56 : Fin 69) = [390, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0056 (by decide)
theorem plane481GenDeadBound0057 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (57 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (57 : Fin 69) = [384, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0057 (by decide)
theorem plane481GenDeadBound0058 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (58 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (58 : Fin 69) = [456, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0058 (by decide)
theorem plane481GenDeadBound0059 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (59 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (59 : Fin 69) = [458, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0059 (by decide)
theorem plane481GenDeadBound0060 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (60 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (60 : Fin 69) = [460, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0060 (by decide)
theorem plane481GenDeadBound0061 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (61 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (61 : Fin 69) = [462, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0061 (by decide)
theorem plane481GenDeadBound0062 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (62 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (62 : Fin 69) = [480, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0062 (by decide)
theorem plane481GenDeadBound0063 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (63 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (63 : Fin 69) = [482, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0063 (by decide)
theorem plane481GenDeadBound0064 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (64 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (64 : Fin 69) = [456, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0064 (by decide)
theorem plane481GenDeadBound0065 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (65 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (65 : Fin 69) = [484, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0065 (by decide)
theorem plane481GenDeadBound0066 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (66 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (66 : Fin 69) = [486, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0066 (by decide)
theorem plane481GenDeadBound0067 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (67 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (67 : Fin 69) = [420, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0067 (by decide)
theorem plane481GenDeadBound0068 :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis (68 : Fin 69))) 17 := by
  rw [show plane481GenDeadBasis (68 : Fin 69) = [418, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane481GenSource0068 (by decide)
theorem plane481GenDeadQRA (d : Fin 69) :
    QuotientRankAtLeast (spanCodes (plane481GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane481GenDeadBound0000
  | ⟨1, _⟩ => plane481GenDeadBound0001
  | ⟨2, _⟩ => plane481GenDeadBound0002
  | ⟨3, _⟩ => plane481GenDeadBound0003
  | ⟨4, _⟩ => plane481GenDeadBound0004
  | ⟨5, _⟩ => plane481GenDeadBound0005
  | ⟨6, _⟩ => plane481GenDeadBound0006
  | ⟨7, _⟩ => plane481GenDeadBound0007
  | ⟨8, _⟩ => plane481GenDeadBound0008
  | ⟨9, _⟩ => plane481GenDeadBound0009
  | ⟨10, _⟩ => plane481GenDeadBound0010
  | ⟨11, _⟩ => plane481GenDeadBound0011
  | ⟨12, _⟩ => plane481GenDeadBound0012
  | ⟨13, _⟩ => plane481GenDeadBound0013
  | ⟨14, _⟩ => plane481GenDeadBound0014
  | ⟨15, _⟩ => plane481GenDeadBound0015
  | ⟨16, _⟩ => plane481GenDeadBound0016
  | ⟨17, _⟩ => plane481GenDeadBound0017
  | ⟨18, _⟩ => plane481GenDeadBound0018
  | ⟨19, _⟩ => plane481GenDeadBound0019
  | ⟨20, _⟩ => plane481GenDeadBound0020
  | ⟨21, _⟩ => plane481GenDeadBound0021
  | ⟨22, _⟩ => plane481GenDeadBound0022
  | ⟨23, _⟩ => plane481GenDeadBound0023
  | ⟨24, _⟩ => plane481GenDeadBound0024
  | ⟨25, _⟩ => plane481GenDeadBound0025
  | ⟨26, _⟩ => plane481GenDeadBound0026
  | ⟨27, _⟩ => plane481GenDeadBound0027
  | ⟨28, _⟩ => plane481GenDeadBound0028
  | ⟨29, _⟩ => plane481GenDeadBound0029
  | ⟨30, _⟩ => plane481GenDeadBound0030
  | ⟨31, _⟩ => plane481GenDeadBound0031
  | ⟨32, _⟩ => plane481GenDeadBound0032
  | ⟨33, _⟩ => plane481GenDeadBound0033
  | ⟨34, _⟩ => plane481GenDeadBound0034
  | ⟨35, _⟩ => plane481GenDeadBound0035
  | ⟨36, _⟩ => plane481GenDeadBound0036
  | ⟨37, _⟩ => plane481GenDeadBound0037
  | ⟨38, _⟩ => plane481GenDeadBound0038
  | ⟨39, _⟩ => plane481GenDeadBound0039
  | ⟨40, _⟩ => plane481GenDeadBound0040
  | ⟨41, _⟩ => plane481GenDeadBound0041
  | ⟨42, _⟩ => plane481GenDeadBound0042
  | ⟨43, _⟩ => plane481GenDeadBound0043
  | ⟨44, _⟩ => plane481GenDeadBound0044
  | ⟨45, _⟩ => plane481GenDeadBound0045
  | ⟨46, _⟩ => plane481GenDeadBound0046
  | ⟨47, _⟩ => plane481GenDeadBound0047
  | ⟨48, _⟩ => plane481GenDeadBound0048
  | ⟨49, _⟩ => plane481GenDeadBound0049
  | ⟨50, _⟩ => plane481GenDeadBound0050
  | ⟨51, _⟩ => plane481GenDeadBound0051
  | ⟨52, _⟩ => plane481GenDeadBound0052
  | ⟨53, _⟩ => plane481GenDeadBound0053
  | ⟨54, _⟩ => plane481GenDeadBound0054
  | ⟨55, _⟩ => plane481GenDeadBound0055
  | ⟨56, _⟩ => plane481GenDeadBound0056
  | ⟨57, _⟩ => plane481GenDeadBound0057
  | ⟨58, _⟩ => plane481GenDeadBound0058
  | ⟨59, _⟩ => plane481GenDeadBound0059
  | ⟨60, _⟩ => plane481GenDeadBound0060
  | ⟨61, _⟩ => plane481GenDeadBound0061
  | ⟨62, _⟩ => plane481GenDeadBound0062
  | ⟨63, _⟩ => plane481GenDeadBound0063
  | ⟨64, _⟩ => plane481GenDeadBound0064
  | ⟨65, _⟩ => plane481GenDeadBound0065
  | ⟨66, _⟩ => plane481GenDeadBound0066
  | ⟨67, _⟩ => plane481GenDeadBound0067
  | ⟨68, _⟩ => plane481GenDeadBound0068
  | ⟨k + 69, h⟩ => by omega
end QiushiMatmul
