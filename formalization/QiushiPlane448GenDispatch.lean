import QiushiPlane448GenBindings00
import QiushiPlane448GenBindings01
import QiushiPlane448GenBindings02
import QiushiPlane448GenBindings03
import QiushiPlane448GenBindings04
import QiushiPlane448GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane448GenSourceQRA (i : Fin 56) :
    QuotientRankAtLeast (spanCodes (plane448GenSourceBasis i)) (plane448GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane448GenBound0000
  | ⟨1, _⟩ => plane448GenBound0001
  | ⟨2, _⟩ => plane448GenBound0002
  | ⟨3, _⟩ => plane448GenBound0003
  | ⟨4, _⟩ => plane448GenBound0004
  | ⟨5, _⟩ => plane448GenBound0005
  | ⟨6, _⟩ => plane448GenBound0006
  | ⟨7, _⟩ => plane448GenBound0007
  | ⟨8, _⟩ => plane448GenBound0008
  | ⟨9, _⟩ => plane448GenBound0009
  | ⟨10, _⟩ => plane448GenBound0010
  | ⟨11, _⟩ => plane448GenBound0011
  | ⟨12, _⟩ => plane448GenBound0012
  | ⟨13, _⟩ => plane448GenBound0013
  | ⟨14, _⟩ => plane448GenBound0014
  | ⟨15, _⟩ => plane448GenBound0015
  | ⟨16, _⟩ => plane448GenBound0016
  | ⟨17, _⟩ => plane448GenBound0017
  | ⟨18, _⟩ => plane448GenBound0018
  | ⟨19, _⟩ => plane448GenBound0019
  | ⟨20, _⟩ => plane448GenBound0020
  | ⟨21, _⟩ => plane448GenBound0021
  | ⟨22, _⟩ => plane448GenBound0022
  | ⟨23, _⟩ => plane448GenBound0023
  | ⟨24, _⟩ => plane448GenBound0024
  | ⟨25, _⟩ => plane448GenBound0025
  | ⟨26, _⟩ => plane448GenBound0026
  | ⟨27, _⟩ => plane448GenBound0027
  | ⟨28, _⟩ => plane448GenBound0028
  | ⟨29, _⟩ => plane448GenBound0029
  | ⟨30, _⟩ => plane448GenBound0030
  | ⟨31, _⟩ => plane448GenBound0031
  | ⟨32, _⟩ => plane448GenBound0032
  | ⟨33, _⟩ => plane448GenBound0033
  | ⟨34, _⟩ => plane448GenBound0034
  | ⟨35, _⟩ => plane448GenBound0035
  | ⟨36, _⟩ => plane448GenBound0036
  | ⟨37, _⟩ => plane448GenBound0037
  | ⟨38, _⟩ => plane448GenBound0038
  | ⟨39, _⟩ => plane448GenBound0039
  | ⟨40, _⟩ => plane448GenBound0040
  | ⟨41, _⟩ => plane448GenBound0041
  | ⟨42, _⟩ => plane448GenBound0042
  | ⟨43, _⟩ => plane448GenBound0043
  | ⟨44, _⟩ => plane448GenBound0044
  | ⟨45, _⟩ => plane448GenBound0045
  | ⟨46, _⟩ => plane448GenBound0046
  | ⟨47, _⟩ => plane448GenBound0047
  | ⟨48, _⟩ => plane448GenBound0048
  | ⟨49, _⟩ => plane448GenBound0049
  | ⟨50, _⟩ => plane448GenBound0050
  | ⟨51, _⟩ => plane448GenBound0051
  | ⟨52, _⟩ => plane448GenBound0052
  | ⟨53, _⟩ => plane448GenBound0053
  | ⟨54, _⟩ => plane448GenBound0054
  | ⟨55, _⟩ => plane448GenBound0055
  | ⟨k + 56, h⟩ => by omega
theorem plane448GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (0 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (0 : Fin 38) = [304, 160, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0000 (by decide)
theorem plane448GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (1 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (1 : Fin 38) = [280, 130, 34, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0001 (by decide)
theorem plane448GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (2 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (2 : Fin 38) = [286, 132, 36, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0002 (by decide)
theorem plane448GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (3 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (3 : Fin 38) = [284, 134, 38, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0003 (by decide)
theorem plane448GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (4 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (4 : Fin 38) = [274, 136, 40, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0004 (by decide)
theorem plane448GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (5 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (5 : Fin 38) = [274, 132, 36, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0005 (by decide)
theorem plane448GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (6 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (6 : Fin 38) = [272, 138, 42, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0006 (by decide)
theorem plane448GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (7 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (7 : Fin 38) = [276, 142, 46, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0007 (by decide)
theorem plane448GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (8 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (8 : Fin 38) = [264, 146, 50, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0008 (by decide)
theorem plane448GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (9 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (9 : Fin 38) = [270, 148, 52, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0009 (by decide)
theorem plane448GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (10 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (10 : Fin 38) = [268, 150, 54, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0010 (by decide)
theorem plane448GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (11 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (11 : Fin 38) = [258, 152, 56, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0011 (by decide)
theorem plane448GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (12 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (12 : Fin 38) = [258, 150, 54, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0012 (by decide)
theorem plane448GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (13 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (13 : Fin 38) = [256, 154, 58, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0013 (by decide)
theorem plane448GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (14 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (14 : Fin 38) = [262, 156, 60, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0014 (by decide)
theorem plane448GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (15 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (15 : Fin 38) = [314, 160, 70, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0015 (by decide)
theorem plane448GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (16 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (16 : Fin 38) = [308, 160, 68, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0016 (by decide)
theorem plane448GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (17 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (17 : Fin 38) = [314, 160, 76, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0017 (by decide)
theorem plane448GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (18 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (18 : Fin 38) = [308, 160, 66, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0018 (by decide)
theorem plane448GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (19 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (19 : Fin 38) = [310, 160, 66, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0019 (by decide)
theorem plane448GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (20 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (20 : Fin 38) = [302, 160, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0020 (by decide)
theorem plane448GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (21 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (21 : Fin 38) = [300, 160, 66, 22, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0021 (by decide)
theorem plane448GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (22 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (22 : Fin 38) = [300, 160, 78, 22, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0022 (by decide)
theorem plane448GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (23 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (23 : Fin 38) = [302, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0023 (by decide)
theorem plane448GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (24 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (24 : Fin 38) = [314, 160, 96, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0024 (by decide)
theorem plane448GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (25 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (25 : Fin 38) = [314, 160, 100, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0025 (by decide)
theorem plane448GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (26 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (26 : Fin 38) = [314, 160, 102, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0026 (by decide)
theorem plane448GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (27 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (27 : Fin 38) = [314, 160, 104, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0027 (by decide)
theorem plane448GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (28 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (28 : Fin 38) = [314, 160, 106, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0028 (by decide)
theorem plane448GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (29 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (29 : Fin 38) = [314, 160, 108, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0029 (by decide)
theorem plane448GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (30 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (30 : Fin 38) = [314, 160, 110, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0030 (by decide)
theorem plane448GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (31 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (31 : Fin 38) = [314, 160, 112, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0031 (by decide)
theorem plane448GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (32 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (32 : Fin 38) = [314, 160, 114, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0032 (by decide)
theorem plane448GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (33 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (33 : Fin 38) = [314, 160, 116, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0033 (by decide)
theorem plane448GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (34 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (34 : Fin 38) = [314, 160, 118, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0034 (by decide)
theorem plane448GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (35 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (35 : Fin 38) = [314, 160, 120, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0035 (by decide)
theorem plane448GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (36 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (36 : Fin 38) = [314, 160, 124, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0036 (by decide)
theorem plane448GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis (37 : Fin 38))) 16 := by
  rw [show plane448GenDeadBasis (37 : Fin 38) = [314, 160, 126, 1] from rfl]
  exact quotientRankAtLeast_weaken plane448GenSource0037 (by decide)
theorem plane448GenDeadQRA (d : Fin 38) :
    QuotientRankAtLeast (spanCodes (plane448GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane448GenDeadBound0000
  | ⟨1, _⟩ => plane448GenDeadBound0001
  | ⟨2, _⟩ => plane448GenDeadBound0002
  | ⟨3, _⟩ => plane448GenDeadBound0003
  | ⟨4, _⟩ => plane448GenDeadBound0004
  | ⟨5, _⟩ => plane448GenDeadBound0005
  | ⟨6, _⟩ => plane448GenDeadBound0006
  | ⟨7, _⟩ => plane448GenDeadBound0007
  | ⟨8, _⟩ => plane448GenDeadBound0008
  | ⟨9, _⟩ => plane448GenDeadBound0009
  | ⟨10, _⟩ => plane448GenDeadBound0010
  | ⟨11, _⟩ => plane448GenDeadBound0011
  | ⟨12, _⟩ => plane448GenDeadBound0012
  | ⟨13, _⟩ => plane448GenDeadBound0013
  | ⟨14, _⟩ => plane448GenDeadBound0014
  | ⟨15, _⟩ => plane448GenDeadBound0015
  | ⟨16, _⟩ => plane448GenDeadBound0016
  | ⟨17, _⟩ => plane448GenDeadBound0017
  | ⟨18, _⟩ => plane448GenDeadBound0018
  | ⟨19, _⟩ => plane448GenDeadBound0019
  | ⟨20, _⟩ => plane448GenDeadBound0020
  | ⟨21, _⟩ => plane448GenDeadBound0021
  | ⟨22, _⟩ => plane448GenDeadBound0022
  | ⟨23, _⟩ => plane448GenDeadBound0023
  | ⟨24, _⟩ => plane448GenDeadBound0024
  | ⟨25, _⟩ => plane448GenDeadBound0025
  | ⟨26, _⟩ => plane448GenDeadBound0026
  | ⟨27, _⟩ => plane448GenDeadBound0027
  | ⟨28, _⟩ => plane448GenDeadBound0028
  | ⟨29, _⟩ => plane448GenDeadBound0029
  | ⟨30, _⟩ => plane448GenDeadBound0030
  | ⟨31, _⟩ => plane448GenDeadBound0031
  | ⟨32, _⟩ => plane448GenDeadBound0032
  | ⟨33, _⟩ => plane448GenDeadBound0033
  | ⟨34, _⟩ => plane448GenDeadBound0034
  | ⟨35, _⟩ => plane448GenDeadBound0035
  | ⟨36, _⟩ => plane448GenDeadBound0036
  | ⟨37, _⟩ => plane448GenDeadBound0037
  | ⟨k + 38, h⟩ => by omega
end QiushiMatmul
