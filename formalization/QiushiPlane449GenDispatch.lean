import QiushiPlane449GenBindings00
import QiushiPlane449GenBindings01
import QiushiPlane449GenBindings02
import QiushiPlane449GenBindings03
import QiushiPlane449GenBindings04
import QiushiPlane449GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane449GenSourceQRA (i : Fin 56) :
    QuotientRankAtLeast (spanCodes (plane449GenSourceBasis i)) (plane449GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane449GenBound0000
  | ⟨1, _⟩ => plane449GenBound0001
  | ⟨2, _⟩ => plane449GenBound0002
  | ⟨3, _⟩ => plane449GenBound0003
  | ⟨4, _⟩ => plane449GenBound0004
  | ⟨5, _⟩ => plane449GenBound0005
  | ⟨6, _⟩ => plane449GenBound0006
  | ⟨7, _⟩ => plane449GenBound0007
  | ⟨8, _⟩ => plane449GenBound0008
  | ⟨9, _⟩ => plane449GenBound0009
  | ⟨10, _⟩ => plane449GenBound0010
  | ⟨11, _⟩ => plane449GenBound0011
  | ⟨12, _⟩ => plane449GenBound0012
  | ⟨13, _⟩ => plane449GenBound0013
  | ⟨14, _⟩ => plane449GenBound0014
  | ⟨15, _⟩ => plane449GenBound0015
  | ⟨16, _⟩ => plane449GenBound0016
  | ⟨17, _⟩ => plane449GenBound0017
  | ⟨18, _⟩ => plane449GenBound0018
  | ⟨19, _⟩ => plane449GenBound0019
  | ⟨20, _⟩ => plane449GenBound0020
  | ⟨21, _⟩ => plane449GenBound0021
  | ⟨22, _⟩ => plane449GenBound0022
  | ⟨23, _⟩ => plane449GenBound0023
  | ⟨24, _⟩ => plane449GenBound0024
  | ⟨25, _⟩ => plane449GenBound0025
  | ⟨26, _⟩ => plane449GenBound0026
  | ⟨27, _⟩ => plane449GenBound0027
  | ⟨28, _⟩ => plane449GenBound0028
  | ⟨29, _⟩ => plane449GenBound0029
  | ⟨30, _⟩ => plane449GenBound0030
  | ⟨31, _⟩ => plane449GenBound0031
  | ⟨32, _⟩ => plane449GenBound0032
  | ⟨33, _⟩ => plane449GenBound0033
  | ⟨34, _⟩ => plane449GenBound0034
  | ⟨35, _⟩ => plane449GenBound0035
  | ⟨36, _⟩ => plane449GenBound0036
  | ⟨37, _⟩ => plane449GenBound0037
  | ⟨38, _⟩ => plane449GenBound0038
  | ⟨39, _⟩ => plane449GenBound0039
  | ⟨40, _⟩ => plane449GenBound0040
  | ⟨41, _⟩ => plane449GenBound0041
  | ⟨42, _⟩ => plane449GenBound0042
  | ⟨43, _⟩ => plane449GenBound0043
  | ⟨44, _⟩ => plane449GenBound0044
  | ⟨45, _⟩ => plane449GenBound0045
  | ⟨46, _⟩ => plane449GenBound0046
  | ⟨47, _⟩ => plane449GenBound0047
  | ⟨48, _⟩ => plane449GenBound0048
  | ⟨49, _⟩ => plane449GenBound0049
  | ⟨50, _⟩ => plane449GenBound0050
  | ⟨51, _⟩ => plane449GenBound0051
  | ⟨52, _⟩ => plane449GenBound0052
  | ⟨53, _⟩ => plane449GenBound0053
  | ⟨54, _⟩ => plane449GenBound0054
  | ⟨55, _⟩ => plane449GenBound0055
  | ⟨k + 56, h⟩ => by omega
theorem plane449GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (0 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (0 : Fin 48) = [310, 160, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0000 (by decide)
theorem plane449GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (1 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (1 : Fin 48) = [306, 160, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0001 (by decide)
theorem plane449GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (2 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (2 : Fin 48) = [316, 160, 68, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0002 (by decide)
theorem plane449GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (3 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (3 : Fin 48) = [316, 160, 70, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0003 (by decide)
theorem plane449GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (4 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (4 : Fin 48) = [316, 160, 74, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0004 (by decide)
theorem plane449GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (5 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (5 : Fin 48) = [316, 160, 76, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0005 (by decide)
theorem plane449GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (6 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (6 : Fin 48) = [316, 160, 110, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0006 (by decide)
theorem plane449GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (7 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (7 : Fin 48) = [304, 160, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0007 (by decide)
theorem plane449GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (8 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (8 : Fin 48) = [300, 160, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0008 (by decide)
theorem plane449GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (9 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (9 : Fin 48) = [302, 160, 18, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0009 (by decide)
theorem plane449GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (10 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (10 : Fin 48) = [290, 160, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0010 (by decide)
theorem plane449GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (11 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (11 : Fin 48) = [290, 160, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0011 (by decide)
theorem plane449GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (12 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (12 : Fin 48) = [286, 130, 34, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0012 (by decide)
theorem plane449GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (13 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (13 : Fin 48) = [280, 132, 36, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0013 (by decide)
theorem plane449GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (14 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (14 : Fin 48) = [276, 136, 40, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0014 (by decide)
theorem plane449GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (15 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (15 : Fin 48) = [276, 134, 38, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0015 (by decide)
theorem plane449GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (16 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (16 : Fin 48) = [278, 138, 42, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0016 (by decide)
theorem plane449GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (17 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (17 : Fin 48) = [274, 132, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0017 (by decide)
theorem plane449GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (18 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (18 : Fin 48) = [270, 146, 50, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0018 (by decide)
theorem plane449GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (19 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (19 : Fin 48) = [266, 150, 54, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0019 (by decide)
theorem plane449GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (20 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (20 : Fin 48) = [262, 142, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0020 (by decide)
theorem plane449GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (21 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (21 : Fin 48) = [262, 148, 52, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0021 (by decide)
theorem plane449GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (22 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (22 : Fin 48) = [256, 156, 60, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0022 (by decide)
theorem plane449GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (23 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (23 : Fin 48) = [258, 158, 62, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0023 (by decide)
theorem plane449GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (24 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (24 : Fin 48) = [316, 160, 66, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0024 (by decide)
theorem plane449GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (25 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (25 : Fin 48) = [316, 160, 78, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0025 (by decide)
theorem plane449GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (26 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (26 : Fin 48) = [316, 160, 80, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0026 (by decide)
theorem plane449GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (27 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (27 : Fin 48) = [300, 160, 66, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0027 (by decide)
theorem plane449GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (28 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (28 : Fin 48) = [298, 160, 68, 22, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0028 (by decide)
theorem plane449GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (29 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (29 : Fin 48) = [316, 160, 84, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0029 (by decide)
theorem plane449GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (30 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (30 : Fin 48) = [296, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0030 (by decide)
theorem plane449GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (31 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (31 : Fin 48) = [290, 160, 70, 30, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0031 (by decide)
theorem plane449GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (32 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (32 : Fin 48) = [316, 160, 90, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0032 (by decide)
theorem plane449GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (33 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (33 : Fin 48) = [316, 160, 92, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0033 (by decide)
theorem plane449GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (34 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (34 : Fin 48) = [296, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0034 (by decide)
theorem plane449GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (35 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (35 : Fin 48) = [316, 160, 96, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0035 (by decide)
theorem plane449GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (36 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (36 : Fin 48) = [316, 160, 100, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0036 (by decide)
theorem plane449GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (37 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (37 : Fin 48) = [286, 130, 68, 34, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0037 (by decide)
theorem plane449GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (38 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (38 : Fin 48) = [274, 142, 70, 46, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0038 (by decide)
theorem plane449GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (39 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (39 : Fin 48) = [274, 142, 68, 46, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0039 (by decide)
theorem plane449GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (40 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (40 : Fin 48) = [276, 136, 68, 40, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0040 (by decide)
theorem plane449GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (41 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (41 : Fin 48) = [270, 146, 66, 50, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0041 (by decide)
theorem plane449GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (42 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (42 : Fin 48) = [264, 148, 70, 52, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0042 (by decide)
theorem plane449GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (43 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (43 : Fin 48) = [266, 150, 66, 54, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0043 (by decide)
theorem plane449GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (44 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (44 : Fin 48) = [264, 148, 66, 52, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0044 (by decide)
theorem plane449GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (45 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (45 : Fin 48) = [316, 160, 122, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0045 (by decide)
theorem plane449GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (46 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (46 : Fin 48) = [316, 160, 124, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0046 (by decide)
theorem plane449GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis (47 : Fin 48))) 16 := by
  rw [show plane449GenDeadBasis (47 : Fin 48) = [256, 156, 66, 60, 1] from rfl]
  exact quotientRankAtLeast_weaken plane449GenSource0047 (by decide)
theorem plane449GenDeadQRA (d : Fin 48) :
    QuotientRankAtLeast (spanCodes (plane449GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane449GenDeadBound0000
  | ⟨1, _⟩ => plane449GenDeadBound0001
  | ⟨2, _⟩ => plane449GenDeadBound0002
  | ⟨3, _⟩ => plane449GenDeadBound0003
  | ⟨4, _⟩ => plane449GenDeadBound0004
  | ⟨5, _⟩ => plane449GenDeadBound0005
  | ⟨6, _⟩ => plane449GenDeadBound0006
  | ⟨7, _⟩ => plane449GenDeadBound0007
  | ⟨8, _⟩ => plane449GenDeadBound0008
  | ⟨9, _⟩ => plane449GenDeadBound0009
  | ⟨10, _⟩ => plane449GenDeadBound0010
  | ⟨11, _⟩ => plane449GenDeadBound0011
  | ⟨12, _⟩ => plane449GenDeadBound0012
  | ⟨13, _⟩ => plane449GenDeadBound0013
  | ⟨14, _⟩ => plane449GenDeadBound0014
  | ⟨15, _⟩ => plane449GenDeadBound0015
  | ⟨16, _⟩ => plane449GenDeadBound0016
  | ⟨17, _⟩ => plane449GenDeadBound0017
  | ⟨18, _⟩ => plane449GenDeadBound0018
  | ⟨19, _⟩ => plane449GenDeadBound0019
  | ⟨20, _⟩ => plane449GenDeadBound0020
  | ⟨21, _⟩ => plane449GenDeadBound0021
  | ⟨22, _⟩ => plane449GenDeadBound0022
  | ⟨23, _⟩ => plane449GenDeadBound0023
  | ⟨24, _⟩ => plane449GenDeadBound0024
  | ⟨25, _⟩ => plane449GenDeadBound0025
  | ⟨26, _⟩ => plane449GenDeadBound0026
  | ⟨27, _⟩ => plane449GenDeadBound0027
  | ⟨28, _⟩ => plane449GenDeadBound0028
  | ⟨29, _⟩ => plane449GenDeadBound0029
  | ⟨30, _⟩ => plane449GenDeadBound0030
  | ⟨31, _⟩ => plane449GenDeadBound0031
  | ⟨32, _⟩ => plane449GenDeadBound0032
  | ⟨33, _⟩ => plane449GenDeadBound0033
  | ⟨34, _⟩ => plane449GenDeadBound0034
  | ⟨35, _⟩ => plane449GenDeadBound0035
  | ⟨36, _⟩ => plane449GenDeadBound0036
  | ⟨37, _⟩ => plane449GenDeadBound0037
  | ⟨38, _⟩ => plane449GenDeadBound0038
  | ⟨39, _⟩ => plane449GenDeadBound0039
  | ⟨40, _⟩ => plane449GenDeadBound0040
  | ⟨41, _⟩ => plane449GenDeadBound0041
  | ⟨42, _⟩ => plane449GenDeadBound0042
  | ⟨43, _⟩ => plane449GenDeadBound0043
  | ⟨44, _⟩ => plane449GenDeadBound0044
  | ⟨45, _⟩ => plane449GenDeadBound0045
  | ⟨46, _⟩ => plane449GenDeadBound0046
  | ⟨47, _⟩ => plane449GenDeadBound0047
  | ⟨k + 48, h⟩ => by omega
end QiushiMatmul
