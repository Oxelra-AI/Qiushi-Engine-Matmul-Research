import QiushiPlane447GenBindings00
import QiushiPlane447GenBindings01
import QiushiPlane447GenBindings02
import QiushiPlane447GenBindings03
import QiushiPlane447GenBindings04
import QiushiPlane447GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane447GenSourceQRA (i : Fin 55) :
    QuotientRankAtLeast (spanCodes (plane447GenSourceBasis i)) (plane447GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane447GenBound0000
  | ⟨1, _⟩ => plane447GenBound0001
  | ⟨2, _⟩ => plane447GenBound0002
  | ⟨3, _⟩ => plane447GenBound0003
  | ⟨4, _⟩ => plane447GenBound0004
  | ⟨5, _⟩ => plane447GenBound0005
  | ⟨6, _⟩ => plane447GenBound0006
  | ⟨7, _⟩ => plane447GenBound0007
  | ⟨8, _⟩ => plane447GenBound0008
  | ⟨9, _⟩ => plane447GenBound0009
  | ⟨10, _⟩ => plane447GenBound0010
  | ⟨11, _⟩ => plane447GenBound0011
  | ⟨12, _⟩ => plane447GenBound0012
  | ⟨13, _⟩ => plane447GenBound0013
  | ⟨14, _⟩ => plane447GenBound0014
  | ⟨15, _⟩ => plane447GenBound0015
  | ⟨16, _⟩ => plane447GenBound0016
  | ⟨17, _⟩ => plane447GenBound0017
  | ⟨18, _⟩ => plane447GenBound0018
  | ⟨19, _⟩ => plane447GenBound0019
  | ⟨20, _⟩ => plane447GenBound0020
  | ⟨21, _⟩ => plane447GenBound0021
  | ⟨22, _⟩ => plane447GenBound0022
  | ⟨23, _⟩ => plane447GenBound0023
  | ⟨24, _⟩ => plane447GenBound0024
  | ⟨25, _⟩ => plane447GenBound0025
  | ⟨26, _⟩ => plane447GenBound0026
  | ⟨27, _⟩ => plane447GenBound0027
  | ⟨28, _⟩ => plane447GenBound0028
  | ⟨29, _⟩ => plane447GenBound0029
  | ⟨30, _⟩ => plane447GenBound0030
  | ⟨31, _⟩ => plane447GenBound0031
  | ⟨32, _⟩ => plane447GenBound0032
  | ⟨33, _⟩ => plane447GenBound0033
  | ⟨34, _⟩ => plane447GenBound0034
  | ⟨35, _⟩ => plane447GenBound0035
  | ⟨36, _⟩ => plane447GenBound0036
  | ⟨37, _⟩ => plane447GenBound0037
  | ⟨38, _⟩ => plane447GenBound0038
  | ⟨39, _⟩ => plane447GenBound0039
  | ⟨40, _⟩ => plane447GenBound0040
  | ⟨41, _⟩ => plane447GenBound0041
  | ⟨42, _⟩ => plane447GenBound0042
  | ⟨43, _⟩ => plane447GenBound0043
  | ⟨44, _⟩ => plane447GenBound0044
  | ⟨45, _⟩ => plane447GenBound0045
  | ⟨46, _⟩ => plane447GenBound0046
  | ⟨47, _⟩ => plane447GenBound0047
  | ⟨48, _⟩ => plane447GenBound0048
  | ⟨49, _⟩ => plane447GenBound0049
  | ⟨50, _⟩ => plane447GenBound0050
  | ⟨51, _⟩ => plane447GenBound0051
  | ⟨52, _⟩ => plane447GenBound0052
  | ⟨53, _⟩ => plane447GenBound0053
  | ⟨54, _⟩ => plane447GenBound0054
  | ⟨k + 55, h⟩ => by omega
theorem plane447GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (0 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (0 : Fin 50) = [306, 160, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0000 (by decide)
theorem plane447GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (1 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (1 : Fin 50) = [306, 160, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0001 (by decide)
theorem plane447GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (2 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (2 : Fin 50) = [306, 160, 66, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0002 (by decide)
theorem plane447GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (3 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (3 : Fin 50) = [306, 160, 68, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0003 (by decide)
theorem plane447GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (4 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (4 : Fin 50) = [306, 160, 74, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0004 (by decide)
theorem plane447GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (5 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (5 : Fin 50) = [306, 160, 78, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0005 (by decide)
theorem plane447GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (6 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (6 : Fin 50) = [290, 160, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0006 (by decide)
theorem plane447GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (7 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (7 : Fin 50) = [294, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0007 (by decide)
theorem plane447GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (8 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (8 : Fin 50) = [292, 160, 22, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0008 (by decide)
theorem plane447GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (9 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (9 : Fin 50) = [298, 160, 24, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0009 (by decide)
theorem plane447GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (10 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (10 : Fin 50) = [296, 160, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0010 (by decide)
theorem plane447GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (11 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (11 : Fin 50) = [290, 160, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0011 (by decide)
theorem plane447GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (12 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (12 : Fin 50) = [290, 160, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0012 (by decide)
theorem plane447GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (13 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (13 : Fin 50) = [290, 160, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0013 (by decide)
theorem plane447GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (14 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (14 : Fin 50) = [282, 136, 40, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0014 (by decide)
theorem plane447GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (15 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (15 : Fin 50) = [276, 134, 38, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0015 (by decide)
theorem plane447GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (16 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (16 : Fin 50) = [276, 134, 38, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0016 (by decide)
theorem plane447GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (17 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (17 : Fin 50) = [286, 140, 44, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0017 (by decide)
theorem plane447GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (18 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (18 : Fin 50) = [262, 138, 42, 30, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0018 (by decide)
theorem plane447GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (19 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (19 : Fin 50) = [262, 142, 46, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0019 (by decide)
theorem plane447GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (20 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (20 : Fin 50) = [266, 152, 56, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0020 (by decide)
theorem plane447GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (21 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (21 : Fin 50) = [264, 134, 38, 28, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0021 (by decide)
theorem plane447GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (22 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (22 : Fin 50) = [270, 134, 38, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0022 (by decide)
theorem plane447GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (23 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (23 : Fin 50) = [268, 158, 62, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0023 (by decide)
theorem plane447GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (24 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (24 : Fin 50) = [306, 160, 70, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0024 (by decide)
theorem plane447GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (25 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (25 : Fin 50) = [306, 160, 66, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0025 (by decide)
theorem plane447GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (26 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (26 : Fin 50) = [294, 160, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0026 (by decide)
theorem plane447GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (27 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (27 : Fin 50) = [306, 160, 82, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0027 (by decide)
theorem plane447GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (28 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (28 : Fin 50) = [306, 160, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0028 (by decide)
theorem plane447GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (29 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (29 : Fin 50) = [294, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0029 (by decide)
theorem plane447GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (30 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (30 : Fin 50) = [296, 160, 66, 26, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0030 (by decide)
theorem plane447GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (31 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (31 : Fin 50) = [306, 160, 90, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0031 (by decide)
theorem plane447GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (32 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (32 : Fin 50) = [300, 160, 66, 30, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0032 (by decide)
theorem plane447GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (33 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (33 : Fin 50) = [306, 160, 94, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0033 (by decide)
theorem plane447GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (34 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (34 : Fin 50) = [306, 160, 96, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0034 (by decide)
theorem plane447GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (35 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (35 : Fin 50) = [306, 160, 98, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0035 (by decide)
theorem plane447GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (36 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (36 : Fin 50) = [276, 134, 66, 38, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0036 (by decide)
theorem plane447GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (37 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (37 : Fin 50) = [286, 140, 74, 44, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0037 (by decide)
theorem plane447GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (38 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (38 : Fin 50) = [280, 138, 66, 42, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0038 (by decide)
theorem plane447GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (39 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (39 : Fin 50) = [306, 160, 106, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0039 (by decide)
theorem plane447GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (40 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (40 : Fin 50) = [306, 160, 108, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0040 (by decide)
theorem plane447GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (41 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (41 : Fin 50) = [280, 138, 68, 42, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0041 (by decide)
theorem plane447GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (42 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (42 : Fin 50) = [262, 148, 68, 52, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0042 (by decide)
theorem plane447GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (43 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (43 : Fin 50) = [306, 160, 114, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0043 (by decide)
theorem plane447GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (44 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (44 : Fin 50) = [264, 154, 78, 58, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0044 (by decide)
theorem plane447GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (45 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (45 : Fin 50) = [306, 160, 118, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0045 (by decide)
theorem plane447GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (46 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (46 : Fin 50) = [306, 160, 120, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0046 (by decide)
theorem plane447GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (47 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (47 : Fin 50) = [306, 160, 122, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0047 (by decide)
theorem plane447GenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (48 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (48 : Fin 50) = [268, 158, 66, 62, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0048 (by decide)
theorem plane447GenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis (49 : Fin 50))) 16 := by
  rw [show plane447GenDeadBasis (49 : Fin 50) = [270, 156, 66, 60, 1] from rfl]
  exact quotientRankAtLeast_weaken plane447GenSource0049 (by decide)
theorem plane447GenDeadQRA (d : Fin 50) :
    QuotientRankAtLeast (spanCodes (plane447GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane447GenDeadBound0000
  | ⟨1, _⟩ => plane447GenDeadBound0001
  | ⟨2, _⟩ => plane447GenDeadBound0002
  | ⟨3, _⟩ => plane447GenDeadBound0003
  | ⟨4, _⟩ => plane447GenDeadBound0004
  | ⟨5, _⟩ => plane447GenDeadBound0005
  | ⟨6, _⟩ => plane447GenDeadBound0006
  | ⟨7, _⟩ => plane447GenDeadBound0007
  | ⟨8, _⟩ => plane447GenDeadBound0008
  | ⟨9, _⟩ => plane447GenDeadBound0009
  | ⟨10, _⟩ => plane447GenDeadBound0010
  | ⟨11, _⟩ => plane447GenDeadBound0011
  | ⟨12, _⟩ => plane447GenDeadBound0012
  | ⟨13, _⟩ => plane447GenDeadBound0013
  | ⟨14, _⟩ => plane447GenDeadBound0014
  | ⟨15, _⟩ => plane447GenDeadBound0015
  | ⟨16, _⟩ => plane447GenDeadBound0016
  | ⟨17, _⟩ => plane447GenDeadBound0017
  | ⟨18, _⟩ => plane447GenDeadBound0018
  | ⟨19, _⟩ => plane447GenDeadBound0019
  | ⟨20, _⟩ => plane447GenDeadBound0020
  | ⟨21, _⟩ => plane447GenDeadBound0021
  | ⟨22, _⟩ => plane447GenDeadBound0022
  | ⟨23, _⟩ => plane447GenDeadBound0023
  | ⟨24, _⟩ => plane447GenDeadBound0024
  | ⟨25, _⟩ => plane447GenDeadBound0025
  | ⟨26, _⟩ => plane447GenDeadBound0026
  | ⟨27, _⟩ => plane447GenDeadBound0027
  | ⟨28, _⟩ => plane447GenDeadBound0028
  | ⟨29, _⟩ => plane447GenDeadBound0029
  | ⟨30, _⟩ => plane447GenDeadBound0030
  | ⟨31, _⟩ => plane447GenDeadBound0031
  | ⟨32, _⟩ => plane447GenDeadBound0032
  | ⟨33, _⟩ => plane447GenDeadBound0033
  | ⟨34, _⟩ => plane447GenDeadBound0034
  | ⟨35, _⟩ => plane447GenDeadBound0035
  | ⟨36, _⟩ => plane447GenDeadBound0036
  | ⟨37, _⟩ => plane447GenDeadBound0037
  | ⟨38, _⟩ => plane447GenDeadBound0038
  | ⟨39, _⟩ => plane447GenDeadBound0039
  | ⟨40, _⟩ => plane447GenDeadBound0040
  | ⟨41, _⟩ => plane447GenDeadBound0041
  | ⟨42, _⟩ => plane447GenDeadBound0042
  | ⟨43, _⟩ => plane447GenDeadBound0043
  | ⟨44, _⟩ => plane447GenDeadBound0044
  | ⟨45, _⟩ => plane447GenDeadBound0045
  | ⟨46, _⟩ => plane447GenDeadBound0046
  | ⟨47, _⟩ => plane447GenDeadBound0047
  | ⟨48, _⟩ => plane447GenDeadBound0048
  | ⟨49, _⟩ => plane447GenDeadBound0049
  | ⟨k + 50, h⟩ => by omega
end QiushiMatmul
