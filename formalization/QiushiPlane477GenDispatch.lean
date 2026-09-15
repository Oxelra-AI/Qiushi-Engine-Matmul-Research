import QiushiPlane477GenBindings00
import QiushiPlane477GenBindings01
import QiushiPlane477GenBindings02
import QiushiPlane477GenBindings03
import QiushiPlane477GenBindings04
import QiushiPlane477GenBindings05
import QiushiPlane477GenBindings06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane477GenSourceQRA (i : Fin 63) :
    QuotientRankAtLeast (spanCodes (plane477GenSourceBasis i)) (plane477GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane477GenBound0000
  | ⟨1, _⟩ => plane477GenBound0001
  | ⟨2, _⟩ => plane477GenBound0002
  | ⟨3, _⟩ => plane477GenBound0003
  | ⟨4, _⟩ => plane477GenBound0004
  | ⟨5, _⟩ => plane477GenBound0005
  | ⟨6, _⟩ => plane477GenBound0006
  | ⟨7, _⟩ => plane477GenBound0007
  | ⟨8, _⟩ => plane477GenBound0008
  | ⟨9, _⟩ => plane477GenBound0009
  | ⟨10, _⟩ => plane477GenBound0010
  | ⟨11, _⟩ => plane477GenBound0011
  | ⟨12, _⟩ => plane477GenBound0012
  | ⟨13, _⟩ => plane477GenBound0013
  | ⟨14, _⟩ => plane477GenBound0014
  | ⟨15, _⟩ => plane477GenBound0015
  | ⟨16, _⟩ => plane477GenBound0016
  | ⟨17, _⟩ => plane477GenBound0017
  | ⟨18, _⟩ => plane477GenBound0018
  | ⟨19, _⟩ => plane477GenBound0019
  | ⟨20, _⟩ => plane477GenBound0020
  | ⟨21, _⟩ => plane477GenBound0021
  | ⟨22, _⟩ => plane477GenBound0022
  | ⟨23, _⟩ => plane477GenBound0023
  | ⟨24, _⟩ => plane477GenBound0024
  | ⟨25, _⟩ => plane477GenBound0025
  | ⟨26, _⟩ => plane477GenBound0026
  | ⟨27, _⟩ => plane477GenBound0027
  | ⟨28, _⟩ => plane477GenBound0028
  | ⟨29, _⟩ => plane477GenBound0029
  | ⟨30, _⟩ => plane477GenBound0030
  | ⟨31, _⟩ => plane477GenBound0031
  | ⟨32, _⟩ => plane477GenBound0032
  | ⟨33, _⟩ => plane477GenBound0033
  | ⟨34, _⟩ => plane477GenBound0034
  | ⟨35, _⟩ => plane477GenBound0035
  | ⟨36, _⟩ => plane477GenBound0036
  | ⟨37, _⟩ => plane477GenBound0037
  | ⟨38, _⟩ => plane477GenBound0038
  | ⟨39, _⟩ => plane477GenBound0039
  | ⟨40, _⟩ => plane477GenBound0040
  | ⟨41, _⟩ => plane477GenBound0041
  | ⟨42, _⟩ => plane477GenBound0042
  | ⟨43, _⟩ => plane477GenBound0043
  | ⟨44, _⟩ => plane477GenBound0044
  | ⟨45, _⟩ => plane477GenBound0045
  | ⟨46, _⟩ => plane477GenBound0046
  | ⟨47, _⟩ => plane477GenBound0047
  | ⟨48, _⟩ => plane477GenBound0048
  | ⟨49, _⟩ => plane477GenBound0049
  | ⟨50, _⟩ => plane477GenBound0050
  | ⟨51, _⟩ => plane477GenBound0051
  | ⟨52, _⟩ => plane477GenBound0052
  | ⟨53, _⟩ => plane477GenBound0053
  | ⟨54, _⟩ => plane477GenBound0054
  | ⟨55, _⟩ => plane477GenBound0055
  | ⟨56, _⟩ => plane477GenBound0056
  | ⟨57, _⟩ => plane477GenBound0057
  | ⟨58, _⟩ => plane477GenBound0058
  | ⟨59, _⟩ => plane477GenBound0059
  | ⟨60, _⟩ => plane477GenBound0060
  | ⟨61, _⟩ => plane477GenBound0061
  | ⟨62, _⟩ => plane477GenBound0062
  | ⟨k + 63, h⟩ => by omega
theorem plane477GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (0 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (0 : Fin 63) = [286, 162, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0000 (by decide)
theorem plane477GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (1 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (1 : Fin 63) = [284, 161, 84, 2] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0001 (by decide)
theorem plane477GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (2 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (2 : Fin 63) = [285, 160, 84, 3] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0002 (by decide)
theorem plane477GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (3 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (3 : Fin 63) = [282, 163, 80, 4] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0003 (by decide)
theorem plane477GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (4 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (4 : Fin 63) = [283, 163, 81, 5] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0004 (by decide)
theorem plane477GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (5 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (5 : Fin 63) = [280, 163, 82, 6] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0005 (by decide)
theorem plane477GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (6 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (6 : Fin 63) = [281, 163, 83, 7] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0006 (by decide)
theorem plane477GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (7 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (7 : Fin 63) = [278, 163, 84, 8] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0007 (by decide)
theorem plane477GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (8 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (8 : Fin 63) = [279, 163, 84, 9] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0008 (by decide)
theorem plane477GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (9 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (9 : Fin 63) = [276, 163, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0009 (by decide)
theorem plane477GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (10 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (10 : Fin 63) = [277, 163, 84, 11] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0010 (by decide)
theorem plane477GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (11 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (11 : Fin 63) = [274, 163, 84, 12] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0011 (by decide)
theorem plane477GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (12 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (12 : Fin 63) = [275, 163, 84, 13] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0012 (by decide)
theorem plane477GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (13 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (13 : Fin 63) = [272, 163, 84, 14] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0013 (by decide)
theorem plane477GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (14 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (14 : Fin 63) = [273, 163, 84, 15] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0014 (by decide)
theorem plane477GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (15 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (15 : Fin 63) = [270, 163, 68, 16] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0015 (by decide)
theorem plane477GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (16 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (16 : Fin 63) = [271, 163, 69, 17] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0016 (by decide)
theorem plane477GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (17 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (17 : Fin 63) = [268, 163, 70, 18] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0017 (by decide)
theorem plane477GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (18 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (18 : Fin 63) = [269, 163, 71, 19] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0018 (by decide)
theorem plane477GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (19 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (19 : Fin 63) = [266, 163, 64, 20] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0019 (by decide)
theorem plane477GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (20 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (20 : Fin 63) = [267, 163, 65, 21] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0020 (by decide)
theorem plane477GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (21 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (21 : Fin 63) = [264, 163, 66, 22] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0021 (by decide)
theorem plane477GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (22 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (22 : Fin 63) = [265, 163, 67, 23] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0022 (by decide)
theorem plane477GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (23 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (23 : Fin 63) = [262, 163, 76, 24] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0023 (by decide)
theorem plane477GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (24 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (24 : Fin 63) = [263, 163, 77, 25] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0024 (by decide)
theorem plane477GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (25 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (25 : Fin 63) = [260, 163, 78, 26] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0025 (by decide)
theorem plane477GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (26 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (26 : Fin 63) = [261, 163, 79, 27] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0026 (by decide)
theorem plane477GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (27 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (27 : Fin 63) = [258, 163, 72, 28] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0027 (by decide)
theorem plane477GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (28 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (28 : Fin 63) = [259, 163, 73, 29] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0028 (by decide)
theorem plane477GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (29 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (29 : Fin 63) = [256, 163, 74, 30] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0029 (by decide)
theorem plane477GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (30 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (30 : Fin 63) = [257, 163, 75, 31] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0030 (by decide)
theorem plane477GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (31 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (31 : Fin 63) = [286, 131, 84, 32] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0031 (by decide)
theorem plane477GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (32 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (32 : Fin 63) = [286, 130, 84, 33] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0032 (by decide)
theorem plane477GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (33 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (33 : Fin 63) = [286, 129, 84, 34] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0033 (by decide)
theorem plane477GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (34 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (34 : Fin 63) = [286, 128, 84, 35] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0034 (by decide)
theorem plane477GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (35 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (35 : Fin 63) = [286, 135, 84, 36] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0035 (by decide)
theorem plane477GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (36 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (36 : Fin 63) = [286, 134, 84, 37] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0036 (by decide)
theorem plane477GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (37 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (37 : Fin 63) = [286, 133, 84, 38] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0037 (by decide)
theorem plane477GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (38 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (38 : Fin 63) = [286, 132, 84, 39] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0038 (by decide)
theorem plane477GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (39 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (39 : Fin 63) = [286, 139, 84, 40] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0039 (by decide)
theorem plane477GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (40 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (40 : Fin 63) = [286, 138, 84, 41] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0040 (by decide)
theorem plane477GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (41 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (41 : Fin 63) = [286, 137, 84, 42] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0041 (by decide)
theorem plane477GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (42 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (42 : Fin 63) = [286, 136, 84, 43] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0042 (by decide)
theorem plane477GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (43 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (43 : Fin 63) = [286, 143, 84, 44] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0043 (by decide)
theorem plane477GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (44 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (44 : Fin 63) = [286, 142, 84, 45] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0044 (by decide)
theorem plane477GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (45 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (45 : Fin 63) = [286, 141, 84, 46] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0045 (by decide)
theorem plane477GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (46 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (46 : Fin 63) = [286, 140, 84, 47] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0046 (by decide)
theorem plane477GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (47 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (47 : Fin 63) = [286, 147, 84, 48] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0047 (by decide)
theorem plane477GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (48 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (48 : Fin 63) = [286, 146, 84, 49] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0048 (by decide)
theorem plane477GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (49 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (49 : Fin 63) = [286, 145, 84, 50] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0049 (by decide)
theorem plane477GenDeadBound0050 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (50 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (50 : Fin 63) = [286, 144, 84, 51] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0050 (by decide)
theorem plane477GenDeadBound0051 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (51 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (51 : Fin 63) = [286, 151, 84, 52] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0051 (by decide)
theorem plane477GenDeadBound0052 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (52 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (52 : Fin 63) = [286, 150, 84, 53] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0052 (by decide)
theorem plane477GenDeadBound0053 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (53 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (53 : Fin 63) = [286, 149, 84, 54] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0053 (by decide)
theorem plane477GenDeadBound0054 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (54 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (54 : Fin 63) = [286, 148, 84, 55] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0054 (by decide)
theorem plane477GenDeadBound0055 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (55 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (55 : Fin 63) = [286, 155, 84, 56] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0055 (by decide)
theorem plane477GenDeadBound0056 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (56 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (56 : Fin 63) = [286, 154, 84, 57] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0056 (by decide)
theorem plane477GenDeadBound0057 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (57 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (57 : Fin 63) = [286, 153, 84, 58] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0057 (by decide)
theorem plane477GenDeadBound0058 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (58 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (58 : Fin 63) = [286, 152, 84, 59] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0058 (by decide)
theorem plane477GenDeadBound0059 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (59 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (59 : Fin 63) = [286, 159, 84, 60] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0059 (by decide)
theorem plane477GenDeadBound0060 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (60 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (60 : Fin 63) = [286, 158, 84, 61] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0060 (by decide)
theorem plane477GenDeadBound0061 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (61 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (61 : Fin 63) = [286, 157, 84, 62] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0061 (by decide)
theorem plane477GenDeadBound0062 :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis (62 : Fin 63))) 17 := by
  rw [show plane477GenDeadBasis (62 : Fin 63) = [286, 156, 84, 63] from rfl]
  exact quotientRankAtLeast_weaken plane477GenSource0062 (by decide)
theorem plane477GenDeadQRA (d : Fin 63) :
    QuotientRankAtLeast (spanCodes (plane477GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane477GenDeadBound0000
  | ⟨1, _⟩ => plane477GenDeadBound0001
  | ⟨2, _⟩ => plane477GenDeadBound0002
  | ⟨3, _⟩ => plane477GenDeadBound0003
  | ⟨4, _⟩ => plane477GenDeadBound0004
  | ⟨5, _⟩ => plane477GenDeadBound0005
  | ⟨6, _⟩ => plane477GenDeadBound0006
  | ⟨7, _⟩ => plane477GenDeadBound0007
  | ⟨8, _⟩ => plane477GenDeadBound0008
  | ⟨9, _⟩ => plane477GenDeadBound0009
  | ⟨10, _⟩ => plane477GenDeadBound0010
  | ⟨11, _⟩ => plane477GenDeadBound0011
  | ⟨12, _⟩ => plane477GenDeadBound0012
  | ⟨13, _⟩ => plane477GenDeadBound0013
  | ⟨14, _⟩ => plane477GenDeadBound0014
  | ⟨15, _⟩ => plane477GenDeadBound0015
  | ⟨16, _⟩ => plane477GenDeadBound0016
  | ⟨17, _⟩ => plane477GenDeadBound0017
  | ⟨18, _⟩ => plane477GenDeadBound0018
  | ⟨19, _⟩ => plane477GenDeadBound0019
  | ⟨20, _⟩ => plane477GenDeadBound0020
  | ⟨21, _⟩ => plane477GenDeadBound0021
  | ⟨22, _⟩ => plane477GenDeadBound0022
  | ⟨23, _⟩ => plane477GenDeadBound0023
  | ⟨24, _⟩ => plane477GenDeadBound0024
  | ⟨25, _⟩ => plane477GenDeadBound0025
  | ⟨26, _⟩ => plane477GenDeadBound0026
  | ⟨27, _⟩ => plane477GenDeadBound0027
  | ⟨28, _⟩ => plane477GenDeadBound0028
  | ⟨29, _⟩ => plane477GenDeadBound0029
  | ⟨30, _⟩ => plane477GenDeadBound0030
  | ⟨31, _⟩ => plane477GenDeadBound0031
  | ⟨32, _⟩ => plane477GenDeadBound0032
  | ⟨33, _⟩ => plane477GenDeadBound0033
  | ⟨34, _⟩ => plane477GenDeadBound0034
  | ⟨35, _⟩ => plane477GenDeadBound0035
  | ⟨36, _⟩ => plane477GenDeadBound0036
  | ⟨37, _⟩ => plane477GenDeadBound0037
  | ⟨38, _⟩ => plane477GenDeadBound0038
  | ⟨39, _⟩ => plane477GenDeadBound0039
  | ⟨40, _⟩ => plane477GenDeadBound0040
  | ⟨41, _⟩ => plane477GenDeadBound0041
  | ⟨42, _⟩ => plane477GenDeadBound0042
  | ⟨43, _⟩ => plane477GenDeadBound0043
  | ⟨44, _⟩ => plane477GenDeadBound0044
  | ⟨45, _⟩ => plane477GenDeadBound0045
  | ⟨46, _⟩ => plane477GenDeadBound0046
  | ⟨47, _⟩ => plane477GenDeadBound0047
  | ⟨48, _⟩ => plane477GenDeadBound0048
  | ⟨49, _⟩ => plane477GenDeadBound0049
  | ⟨50, _⟩ => plane477GenDeadBound0050
  | ⟨51, _⟩ => plane477GenDeadBound0051
  | ⟨52, _⟩ => plane477GenDeadBound0052
  | ⟨53, _⟩ => plane477GenDeadBound0053
  | ⟨54, _⟩ => plane477GenDeadBound0054
  | ⟨55, _⟩ => plane477GenDeadBound0055
  | ⟨56, _⟩ => plane477GenDeadBound0056
  | ⟨57, _⟩ => plane477GenDeadBound0057
  | ⟨58, _⟩ => plane477GenDeadBound0058
  | ⟨59, _⟩ => plane477GenDeadBound0059
  | ⟨60, _⟩ => plane477GenDeadBound0060
  | ⟨61, _⟩ => plane477GenDeadBound0061
  | ⟨62, _⟩ => plane477GenDeadBound0062
  | ⟨k + 63, h⟩ => by omega
end QiushiMatmul
