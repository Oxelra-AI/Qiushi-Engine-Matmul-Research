import QiushiPlane483GenBindings00
import QiushiPlane483GenBindings01
import QiushiPlane483GenBindings02
import QiushiPlane483GenBindings03
import QiushiPlane483GenBindings04
import QiushiPlane483GenBindings05
import QiushiPlane483GenBindings06
import QiushiPlane483GenBindings07
import QiushiPlane483GenBindings08
import QiushiPlane483GenBindings09
import QiushiPlane483GenBindings10
import QiushiPlane483GenBindings11
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane483GenSourceQRA (i : Fin 112) :
    QuotientRankAtLeast (spanCodes (plane483GenSourceBasis i)) (plane483GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane483GenBound0000
  | ⟨1, _⟩ => plane483GenBound0001
  | ⟨2, _⟩ => plane483GenBound0002
  | ⟨3, _⟩ => plane483GenBound0003
  | ⟨4, _⟩ => plane483GenBound0004
  | ⟨5, _⟩ => plane483GenBound0005
  | ⟨6, _⟩ => plane483GenBound0006
  | ⟨7, _⟩ => plane483GenBound0007
  | ⟨8, _⟩ => plane483GenBound0008
  | ⟨9, _⟩ => plane483GenBound0009
  | ⟨10, _⟩ => plane483GenBound0010
  | ⟨11, _⟩ => plane483GenBound0011
  | ⟨12, _⟩ => plane483GenBound0012
  | ⟨13, _⟩ => plane483GenBound0013
  | ⟨14, _⟩ => plane483GenBound0014
  | ⟨15, _⟩ => plane483GenBound0015
  | ⟨16, _⟩ => plane483GenBound0016
  | ⟨17, _⟩ => plane483GenBound0017
  | ⟨18, _⟩ => plane483GenBound0018
  | ⟨19, _⟩ => plane483GenBound0019
  | ⟨20, _⟩ => plane483GenBound0020
  | ⟨21, _⟩ => plane483GenBound0021
  | ⟨22, _⟩ => plane483GenBound0022
  | ⟨23, _⟩ => plane483GenBound0023
  | ⟨24, _⟩ => plane483GenBound0024
  | ⟨25, _⟩ => plane483GenBound0025
  | ⟨26, _⟩ => plane483GenBound0026
  | ⟨27, _⟩ => plane483GenBound0027
  | ⟨28, _⟩ => plane483GenBound0028
  | ⟨29, _⟩ => plane483GenBound0029
  | ⟨30, _⟩ => plane483GenBound0030
  | ⟨31, _⟩ => plane483GenBound0031
  | ⟨32, _⟩ => plane483GenBound0032
  | ⟨33, _⟩ => plane483GenBound0033
  | ⟨34, _⟩ => plane483GenBound0034
  | ⟨35, _⟩ => plane483GenBound0035
  | ⟨36, _⟩ => plane483GenBound0036
  | ⟨37, _⟩ => plane483GenBound0037
  | ⟨38, _⟩ => plane483GenBound0038
  | ⟨39, _⟩ => plane483GenBound0039
  | ⟨40, _⟩ => plane483GenBound0040
  | ⟨41, _⟩ => plane483GenBound0041
  | ⟨42, _⟩ => plane483GenBound0042
  | ⟨43, _⟩ => plane483GenBound0043
  | ⟨44, _⟩ => plane483GenBound0044
  | ⟨45, _⟩ => plane483GenBound0045
  | ⟨46, _⟩ => plane483GenBound0046
  | ⟨47, _⟩ => plane483GenBound0047
  | ⟨48, _⟩ => plane483GenBound0048
  | ⟨49, _⟩ => plane483GenBound0049
  | ⟨50, _⟩ => plane483GenBound0050
  | ⟨51, _⟩ => plane483GenBound0051
  | ⟨52, _⟩ => plane483GenBound0052
  | ⟨53, _⟩ => plane483GenBound0053
  | ⟨54, _⟩ => plane483GenBound0054
  | ⟨55, _⟩ => plane483GenBound0055
  | ⟨56, _⟩ => plane483GenBound0056
  | ⟨57, _⟩ => plane483GenBound0057
  | ⟨58, _⟩ => plane483GenBound0058
  | ⟨59, _⟩ => plane483GenBound0059
  | ⟨60, _⟩ => plane483GenBound0060
  | ⟨61, _⟩ => plane483GenBound0061
  | ⟨62, _⟩ => plane483GenBound0062
  | ⟨63, _⟩ => plane483GenBound0063
  | ⟨64, _⟩ => plane483GenBound0064
  | ⟨65, _⟩ => plane483GenBound0065
  | ⟨66, _⟩ => plane483GenBound0066
  | ⟨67, _⟩ => plane483GenBound0067
  | ⟨68, _⟩ => plane483GenBound0068
  | ⟨69, _⟩ => plane483GenBound0069
  | ⟨70, _⟩ => plane483GenBound0070
  | ⟨71, _⟩ => plane483GenBound0071
  | ⟨72, _⟩ => plane483GenBound0072
  | ⟨73, _⟩ => plane483GenBound0073
  | ⟨74, _⟩ => plane483GenBound0074
  | ⟨75, _⟩ => plane483GenBound0075
  | ⟨76, _⟩ => plane483GenBound0076
  | ⟨77, _⟩ => plane483GenBound0077
  | ⟨78, _⟩ => plane483GenBound0078
  | ⟨79, _⟩ => plane483GenBound0079
  | ⟨80, _⟩ => plane483GenBound0080
  | ⟨81, _⟩ => plane483GenBound0081
  | ⟨82, _⟩ => plane483GenBound0082
  | ⟨83, _⟩ => plane483GenBound0083
  | ⟨84, _⟩ => plane483GenBound0084
  | ⟨85, _⟩ => plane483GenBound0085
  | ⟨86, _⟩ => plane483GenBound0086
  | ⟨87, _⟩ => plane483GenBound0087
  | ⟨88, _⟩ => plane483GenBound0088
  | ⟨89, _⟩ => plane483GenBound0089
  | ⟨90, _⟩ => plane483GenBound0090
  | ⟨91, _⟩ => plane483GenBound0091
  | ⟨92, _⟩ => plane483GenBound0092
  | ⟨93, _⟩ => plane483GenBound0093
  | ⟨94, _⟩ => plane483GenBound0094
  | ⟨95, _⟩ => plane483GenBound0095
  | ⟨96, _⟩ => plane483GenBound0096
  | ⟨97, _⟩ => plane483GenBound0097
  | ⟨98, _⟩ => plane483GenBound0098
  | ⟨99, _⟩ => plane483GenBound0099
  | ⟨100, _⟩ => plane483GenBound0100
  | ⟨101, _⟩ => plane483GenBound0101
  | ⟨102, _⟩ => plane483GenBound0102
  | ⟨103, _⟩ => plane483GenBound0103
  | ⟨104, _⟩ => plane483GenBound0104
  | ⟨105, _⟩ => plane483GenBound0105
  | ⟨106, _⟩ => plane483GenBound0106
  | ⟨107, _⟩ => plane483GenBound0107
  | ⟨108, _⟩ => plane483GenBound0108
  | ⟨109, _⟩ => plane483GenBound0109
  | ⟨110, _⟩ => plane483GenBound0110
  | ⟨111, _⟩ => plane483GenBound0111
  | ⟨k + 112, h⟩ => by omega
theorem plane483GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (0 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (0 : Fin 76) = [160, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0000 (by decide)
theorem plane483GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (1 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (1 : Fin 76) = [160, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0001 (by decide)
theorem plane483GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (2 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (2 : Fin 76) = [160, 6, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0002 (by decide)
theorem plane483GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (3 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (3 : Fin 76) = [160, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0003 (by decide)
theorem plane483GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (4 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (4 : Fin 76) = [160, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0004 (by decide)
theorem plane483GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (5 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (5 : Fin 76) = [160, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0005 (by decide)
theorem plane483GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (6 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (6 : Fin 76) = [160, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0006 (by decide)
theorem plane483GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (7 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (7 : Fin 76) = [160, 28, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0007 (by decide)
theorem plane483GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (8 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (8 : Fin 76) = [160, 30, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0008 (by decide)
theorem plane483GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (9 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (9 : Fin 76) = [132, 36, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0009 (by decide)
theorem plane483GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (10 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (10 : Fin 76) = [138, 42, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0010 (by decide)
theorem plane483GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (11 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (11 : Fin 76) = [142, 46, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0011 (by decide)
theorem plane483GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (12 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (12 : Fin 76) = [150, 54, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0012 (by decide)
theorem plane483GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (13 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (13 : Fin 76) = [154, 58, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0013 (by decide)
theorem plane483GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (14 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (14 : Fin 76) = [156, 60, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0014 (by decide)
theorem plane483GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (15 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (15 : Fin 76) = [160, 64, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0015 (by decide)
theorem plane483GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (16 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (16 : Fin 76) = [160, 68, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0016 (by decide)
theorem plane483GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (17 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (17 : Fin 76) = [160, 72, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0017 (by decide)
theorem plane483GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (18 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (18 : Fin 76) = [160, 78, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0018 (by decide)
theorem plane483GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (19 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (19 : Fin 76) = [160, 82, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0019 (by decide)
theorem plane483GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (20 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (20 : Fin 76) = [160, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0020 (by decide)
theorem plane483GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (21 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (21 : Fin 76) = [160, 86, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0021 (by decide)
theorem plane483GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (22 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (22 : Fin 76) = [160, 90, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0022 (by decide)
theorem plane483GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (23 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (23 : Fin 76) = [160, 92, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0023 (by decide)
theorem plane483GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (24 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (24 : Fin 76) = [160, 94, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0024 (by decide)
theorem plane483GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (25 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (25 : Fin 76) = [130, 66, 34, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0025 (by decide)
theorem plane483GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (26 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (26 : Fin 76) = [160, 100, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0026 (by decide)
theorem plane483GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (27 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (27 : Fin 76) = [160, 102, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0027 (by decide)
theorem plane483GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (28 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (28 : Fin 76) = [160, 106, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0028 (by decide)
theorem plane483GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (29 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (29 : Fin 76) = [160, 108, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0029 (by decide)
theorem plane483GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (30 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (30 : Fin 76) = [160, 114, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0030 (by decide)
theorem plane483GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (31 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (31 : Fin 76) = [160, 118, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0031 (by decide)
theorem plane483GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (32 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (32 : Fin 76) = [146, 74, 50, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0032 (by decide)
theorem plane483GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (33 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (33 : Fin 76) = [160, 124, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0033 (by decide)
theorem plane483GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (34 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (34 : Fin 76) = [160, 126, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0034 (by decide)
theorem plane483GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (35 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (35 : Fin 76) = [256, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0035 (by decide)
theorem plane483GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (36 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (36 : Fin 76) = [266, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0036 (by decide)
theorem plane483GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (37 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (37 : Fin 76) = [268, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0037 (by decide)
theorem plane483GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (38 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (38 : Fin 76) = [270, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0038 (by decide)
theorem plane483GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (39 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (39 : Fin 76) = [272, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0039 (by decide)
theorem plane483GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (40 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (40 : Fin 76) = [282, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0040 (by decide)
theorem plane483GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (41 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (41 : Fin 76) = [284, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0041 (by decide)
theorem plane483GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (42 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (42 : Fin 76) = [286, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0042 (by decide)
theorem plane483GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (43 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (43 : Fin 76) = [300, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0043 (by decide)
theorem plane483GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (44 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (44 : Fin 76) = [302, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0044 (by decide)
theorem plane483GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (45 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (45 : Fin 76) = [304, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0045 (by decide)
theorem plane483GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (46 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (46 : Fin 76) = [308, 160, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0046 (by decide)
theorem plane483GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (47 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (47 : Fin 76) = [310, 160, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0047 (by decide)
theorem plane483GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (48 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (48 : Fin 76) = [306, 160, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0048 (by decide)
theorem plane483GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (49 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (49 : Fin 76) = [306, 160, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0049 (by decide)
theorem plane483GenDeadBound0050 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (50 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (50 : Fin 76) = [322, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0050 (by decide)
theorem plane483GenDeadBound0051 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (51 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (51 : Fin 76) = [324, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0051 (by decide)
theorem plane483GenDeadBound0052 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (52 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (52 : Fin 76) = [326, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0052 (by decide)
theorem plane483GenDeadBound0053 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (53 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (53 : Fin 76) = [330, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0053 (by decide)
theorem plane483GenDeadBound0054 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (54 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (54 : Fin 76) = [318, 160, 116, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0054 (by decide)
theorem plane483GenDeadBound0055 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (55 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (55 : Fin 76) = [332, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0055 (by decide)
theorem plane483GenDeadBound0056 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (56 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (56 : Fin 76) = [334, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0056 (by decide)
theorem plane483GenDeadBound0057 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (57 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (57 : Fin 76) = [338, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0057 (by decide)
theorem plane483GenDeadBound0058 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (58 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (58 : Fin 76) = [316, 160, 110, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0058 (by decide)
theorem plane483GenDeadBound0059 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (59 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (59 : Fin 76) = [340, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0059 (by decide)
theorem plane483GenDeadBound0060 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (60 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (60 : Fin 76) = [342, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0060 (by decide)
theorem plane483GenDeadBound0061 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (61 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (61 : Fin 76) = [346, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0061 (by decide)
theorem plane483GenDeadBound0062 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (62 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (62 : Fin 76) = [348, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0062 (by decide)
theorem plane483GenDeadBound0063 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (63 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (63 : Fin 76) = [350, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0063 (by decide)
theorem plane483GenDeadBound0064 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (64 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (64 : Fin 76) = [294, 160, 70, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0064 (by decide)
theorem plane483GenDeadBound0065 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (65 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (65 : Fin 76) = [354, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0065 (by decide)
theorem plane483GenDeadBound0066 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (66 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (66 : Fin 76) = [356, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0066 (by decide)
theorem plane483GenDeadBound0067 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (67 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (67 : Fin 76) = [292, 160, 76, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0067 (by decide)
theorem plane483GenDeadBound0068 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (68 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (68 : Fin 76) = [362, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0068 (by decide)
theorem plane483GenDeadBound0069 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (69 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (69 : Fin 76) = [366, 160, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0069 (by decide)
theorem plane483GenDeadBound0070 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (70 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (70 : Fin 76) = [306, 160, 66, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0070 (by decide)
theorem plane483GenDeadBound0071 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (71 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (71 : Fin 76) = [284, 160, 110, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0071 (by decide)
theorem plane483GenDeadBound0072 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (72 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (72 : Fin 76) = [298, 160, 92, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0072 (by decide)
theorem plane483GenDeadBound0073 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (73 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (73 : Fin 76) = [306, 160, 74, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0073 (by decide)
theorem plane483GenDeadBound0074 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (74 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (74 : Fin 76) = [270, 160, 116, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0074 (by decide)
theorem plane483GenDeadBound0075 :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis (75 : Fin 76))) 17 := by
  rw [show plane483GenDeadBasis (75 : Fin 76) = [298, 160, 86, 1] from rfl]
  exact quotientRankAtLeast_weaken plane483GenSource0075 (by decide)
theorem plane483GenDeadQRA (d : Fin 76) :
    QuotientRankAtLeast (spanCodes (plane483GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane483GenDeadBound0000
  | ⟨1, _⟩ => plane483GenDeadBound0001
  | ⟨2, _⟩ => plane483GenDeadBound0002
  | ⟨3, _⟩ => plane483GenDeadBound0003
  | ⟨4, _⟩ => plane483GenDeadBound0004
  | ⟨5, _⟩ => plane483GenDeadBound0005
  | ⟨6, _⟩ => plane483GenDeadBound0006
  | ⟨7, _⟩ => plane483GenDeadBound0007
  | ⟨8, _⟩ => plane483GenDeadBound0008
  | ⟨9, _⟩ => plane483GenDeadBound0009
  | ⟨10, _⟩ => plane483GenDeadBound0010
  | ⟨11, _⟩ => plane483GenDeadBound0011
  | ⟨12, _⟩ => plane483GenDeadBound0012
  | ⟨13, _⟩ => plane483GenDeadBound0013
  | ⟨14, _⟩ => plane483GenDeadBound0014
  | ⟨15, _⟩ => plane483GenDeadBound0015
  | ⟨16, _⟩ => plane483GenDeadBound0016
  | ⟨17, _⟩ => plane483GenDeadBound0017
  | ⟨18, _⟩ => plane483GenDeadBound0018
  | ⟨19, _⟩ => plane483GenDeadBound0019
  | ⟨20, _⟩ => plane483GenDeadBound0020
  | ⟨21, _⟩ => plane483GenDeadBound0021
  | ⟨22, _⟩ => plane483GenDeadBound0022
  | ⟨23, _⟩ => plane483GenDeadBound0023
  | ⟨24, _⟩ => plane483GenDeadBound0024
  | ⟨25, _⟩ => plane483GenDeadBound0025
  | ⟨26, _⟩ => plane483GenDeadBound0026
  | ⟨27, _⟩ => plane483GenDeadBound0027
  | ⟨28, _⟩ => plane483GenDeadBound0028
  | ⟨29, _⟩ => plane483GenDeadBound0029
  | ⟨30, _⟩ => plane483GenDeadBound0030
  | ⟨31, _⟩ => plane483GenDeadBound0031
  | ⟨32, _⟩ => plane483GenDeadBound0032
  | ⟨33, _⟩ => plane483GenDeadBound0033
  | ⟨34, _⟩ => plane483GenDeadBound0034
  | ⟨35, _⟩ => plane483GenDeadBound0035
  | ⟨36, _⟩ => plane483GenDeadBound0036
  | ⟨37, _⟩ => plane483GenDeadBound0037
  | ⟨38, _⟩ => plane483GenDeadBound0038
  | ⟨39, _⟩ => plane483GenDeadBound0039
  | ⟨40, _⟩ => plane483GenDeadBound0040
  | ⟨41, _⟩ => plane483GenDeadBound0041
  | ⟨42, _⟩ => plane483GenDeadBound0042
  | ⟨43, _⟩ => plane483GenDeadBound0043
  | ⟨44, _⟩ => plane483GenDeadBound0044
  | ⟨45, _⟩ => plane483GenDeadBound0045
  | ⟨46, _⟩ => plane483GenDeadBound0046
  | ⟨47, _⟩ => plane483GenDeadBound0047
  | ⟨48, _⟩ => plane483GenDeadBound0048
  | ⟨49, _⟩ => plane483GenDeadBound0049
  | ⟨50, _⟩ => plane483GenDeadBound0050
  | ⟨51, _⟩ => plane483GenDeadBound0051
  | ⟨52, _⟩ => plane483GenDeadBound0052
  | ⟨53, _⟩ => plane483GenDeadBound0053
  | ⟨54, _⟩ => plane483GenDeadBound0054
  | ⟨55, _⟩ => plane483GenDeadBound0055
  | ⟨56, _⟩ => plane483GenDeadBound0056
  | ⟨57, _⟩ => plane483GenDeadBound0057
  | ⟨58, _⟩ => plane483GenDeadBound0058
  | ⟨59, _⟩ => plane483GenDeadBound0059
  | ⟨60, _⟩ => plane483GenDeadBound0060
  | ⟨61, _⟩ => plane483GenDeadBound0061
  | ⟨62, _⟩ => plane483GenDeadBound0062
  | ⟨63, _⟩ => plane483GenDeadBound0063
  | ⟨64, _⟩ => plane483GenDeadBound0064
  | ⟨65, _⟩ => plane483GenDeadBound0065
  | ⟨66, _⟩ => plane483GenDeadBound0066
  | ⟨67, _⟩ => plane483GenDeadBound0067
  | ⟨68, _⟩ => plane483GenDeadBound0068
  | ⟨69, _⟩ => plane483GenDeadBound0069
  | ⟨70, _⟩ => plane483GenDeadBound0070
  | ⟨71, _⟩ => plane483GenDeadBound0071
  | ⟨72, _⟩ => plane483GenDeadBound0072
  | ⟨73, _⟩ => plane483GenDeadBound0073
  | ⟨74, _⟩ => plane483GenDeadBound0074
  | ⟨75, _⟩ => plane483GenDeadBound0075
  | ⟨k + 76, h⟩ => by omega
end QiushiMatmul
