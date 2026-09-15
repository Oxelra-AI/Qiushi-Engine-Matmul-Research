import QiushiPlane439GenBindings00
import QiushiPlane439GenBindings01
import QiushiPlane439GenBindings02
import QiushiPlane439GenBindings03
import QiushiPlane439GenBindings04
import QiushiPlane439GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane439GenSourceQRA (i : Fin 59) :
    QuotientRankAtLeast (spanCodes (plane439GenSourceBasis i)) (plane439GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane439GenBound0000
  | ⟨1, _⟩ => plane439GenBound0001
  | ⟨2, _⟩ => plane439GenBound0002
  | ⟨3, _⟩ => plane439GenBound0003
  | ⟨4, _⟩ => plane439GenBound0004
  | ⟨5, _⟩ => plane439GenBound0005
  | ⟨6, _⟩ => plane439GenBound0006
  | ⟨7, _⟩ => plane439GenBound0007
  | ⟨8, _⟩ => plane439GenBound0008
  | ⟨9, _⟩ => plane439GenBound0009
  | ⟨10, _⟩ => plane439GenBound0010
  | ⟨11, _⟩ => plane439GenBound0011
  | ⟨12, _⟩ => plane439GenBound0012
  | ⟨13, _⟩ => plane439GenBound0013
  | ⟨14, _⟩ => plane439GenBound0014
  | ⟨15, _⟩ => plane439GenBound0015
  | ⟨16, _⟩ => plane439GenBound0016
  | ⟨17, _⟩ => plane439GenBound0017
  | ⟨18, _⟩ => plane439GenBound0018
  | ⟨19, _⟩ => plane439GenBound0019
  | ⟨20, _⟩ => plane439GenBound0020
  | ⟨21, _⟩ => plane439GenBound0021
  | ⟨22, _⟩ => plane439GenBound0022
  | ⟨23, _⟩ => plane439GenBound0023
  | ⟨24, _⟩ => plane439GenBound0024
  | ⟨25, _⟩ => plane439GenBound0025
  | ⟨26, _⟩ => plane439GenBound0026
  | ⟨27, _⟩ => plane439GenBound0027
  | ⟨28, _⟩ => plane439GenBound0028
  | ⟨29, _⟩ => plane439GenBound0029
  | ⟨30, _⟩ => plane439GenBound0030
  | ⟨31, _⟩ => plane439GenBound0031
  | ⟨32, _⟩ => plane439GenBound0032
  | ⟨33, _⟩ => plane439GenBound0033
  | ⟨34, _⟩ => plane439GenBound0034
  | ⟨35, _⟩ => plane439GenBound0035
  | ⟨36, _⟩ => plane439GenBound0036
  | ⟨37, _⟩ => plane439GenBound0037
  | ⟨38, _⟩ => plane439GenBound0038
  | ⟨39, _⟩ => plane439GenBound0039
  | ⟨40, _⟩ => plane439GenBound0040
  | ⟨41, _⟩ => plane439GenBound0041
  | ⟨42, _⟩ => plane439GenBound0042
  | ⟨43, _⟩ => plane439GenBound0043
  | ⟨44, _⟩ => plane439GenBound0044
  | ⟨45, _⟩ => plane439GenBound0045
  | ⟨46, _⟩ => plane439GenBound0046
  | ⟨47, _⟩ => plane439GenBound0047
  | ⟨48, _⟩ => plane439GenBound0048
  | ⟨49, _⟩ => plane439GenBound0049
  | ⟨50, _⟩ => plane439GenBound0050
  | ⟨51, _⟩ => plane439GenBound0051
  | ⟨52, _⟩ => plane439GenBound0052
  | ⟨53, _⟩ => plane439GenBound0053
  | ⟨54, _⟩ => plane439GenBound0054
  | ⟨55, _⟩ => plane439GenBound0055
  | ⟨56, _⟩ => plane439GenBound0056
  | ⟨57, _⟩ => plane439GenBound0057
  | ⟨58, _⟩ => plane439GenBound0058
  | ⟨k + 59, h⟩ => by omega
theorem plane439GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (0 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (0 : Fin 48) = [160, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0000 (by decide)
theorem plane439GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (1 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (1 : Fin 48) = [160, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0001 (by decide)
theorem plane439GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (2 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (2 : Fin 48) = [136, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0002 (by decide)
theorem plane439GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (3 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (3 : Fin 48) = [138, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0003 (by decide)
theorem plane439GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (4 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (4 : Fin 48) = [142, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0004 (by decide)
theorem plane439GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (5 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (5 : Fin 48) = [160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0005 (by decide)
theorem plane439GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (6 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (6 : Fin 48) = [160, 68, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0006 (by decide)
theorem plane439GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (7 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (7 : Fin 48) = [160, 70, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0007 (by decide)
theorem plane439GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (8 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (8 : Fin 48) = [160, 66, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0008 (by decide)
theorem plane439GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (9 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (9 : Fin 48) = [160, 70, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0009 (by decide)
theorem plane439GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (10 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (10 : Fin 48) = [160, 66, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0010 (by decide)
theorem plane439GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (11 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (11 : Fin 48) = [160, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0011 (by decide)
theorem plane439GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (12 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (12 : Fin 48) = [160, 98, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0012 (by decide)
theorem plane439GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (13 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (13 : Fin 48) = [142, 74, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0013 (by decide)
theorem plane439GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (14 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (14 : Fin 48) = [138, 76, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0014 (by decide)
theorem plane439GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (15 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (15 : Fin 48) = [138, 66, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0015 (by decide)
theorem plane439GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (16 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (16 : Fin 48) = [134, 78, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0016 (by decide)
theorem plane439GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (17 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (17 : Fin 48) = [136, 66, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0017 (by decide)
theorem plane439GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (18 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (18 : Fin 48) = [160, 110, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0018 (by decide)
theorem plane439GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (19 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (19 : Fin 48) = [256, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0019 (by decide)
theorem plane439GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (20 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (20 : Fin 48) = [258, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0020 (by decide)
theorem plane439GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (21 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (21 : Fin 48) = [262, 160, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0021 (by decide)
theorem plane439GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (22 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (22 : Fin 48) = [262, 160, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0022 (by decide)
theorem plane439GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (23 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (23 : Fin 48) = [266, 136, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0023 (by decide)
theorem plane439GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (24 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (24 : Fin 48) = [292, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0024 (by decide)
theorem plane439GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (25 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (25 : Fin 48) = [294, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0025 (by decide)
theorem plane439GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (26 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (26 : Fin 48) = [262, 142, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0026 (by decide)
theorem plane439GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (27 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (27 : Fin 48) = [262, 138, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0027 (by decide)
theorem plane439GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (28 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (28 : Fin 48) = [320, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0028 (by decide)
theorem plane439GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (29 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (29 : Fin 48) = [256, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0029 (by decide)
theorem plane439GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (30 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (30 : Fin 48) = [264, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0030 (by decide)
theorem plane439GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (31 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (31 : Fin 48) = [270, 160, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0031 (by decide)
theorem plane439GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (32 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (32 : Fin 48) = [298, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0032 (by decide)
theorem plane439GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (33 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (33 : Fin 48) = [324, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0033 (by decide)
theorem plane439GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (34 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (34 : Fin 48) = [256, 160, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0034 (by decide)
theorem plane439GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (35 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (35 : Fin 48) = [302, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0035 (by decide)
theorem plane439GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (36 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (36 : Fin 48) = [258, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0036 (by decide)
theorem plane439GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (37 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (37 : Fin 48) = [330, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0037 (by decide)
theorem plane439GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (38 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (38 : Fin 48) = [332, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0038 (by decide)
theorem plane439GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (39 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (39 : Fin 48) = [334, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0039 (by decide)
theorem plane439GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (40 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (40 : Fin 48) = [352, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0040 (by decide)
theorem plane439GenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (41 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (41 : Fin 48) = [262, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0041 (by decide)
theorem plane439GenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (42 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (42 : Fin 48) = [256, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0042 (by decide)
theorem plane439GenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (43 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (43 : Fin 48) = [358, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0043 (by decide)
theorem plane439GenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (44 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (44 : Fin 48) = [360, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0044 (by decide)
theorem plane439GenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (45 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (45 : Fin 48) = [362, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0045 (by decide)
theorem plane439GenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (46 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (46 : Fin 48) = [364, 160, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0046 (by decide)
theorem plane439GenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis (47 : Fin 48))) 16 := by
  rw [show plane439GenDeadBasis (47 : Fin 48) = [262, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane439GenSource0047 (by decide)
theorem plane439GenDeadQRA (d : Fin 48) :
    QuotientRankAtLeast (spanCodes (plane439GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane439GenDeadBound0000
  | ⟨1, _⟩ => plane439GenDeadBound0001
  | ⟨2, _⟩ => plane439GenDeadBound0002
  | ⟨3, _⟩ => plane439GenDeadBound0003
  | ⟨4, _⟩ => plane439GenDeadBound0004
  | ⟨5, _⟩ => plane439GenDeadBound0005
  | ⟨6, _⟩ => plane439GenDeadBound0006
  | ⟨7, _⟩ => plane439GenDeadBound0007
  | ⟨8, _⟩ => plane439GenDeadBound0008
  | ⟨9, _⟩ => plane439GenDeadBound0009
  | ⟨10, _⟩ => plane439GenDeadBound0010
  | ⟨11, _⟩ => plane439GenDeadBound0011
  | ⟨12, _⟩ => plane439GenDeadBound0012
  | ⟨13, _⟩ => plane439GenDeadBound0013
  | ⟨14, _⟩ => plane439GenDeadBound0014
  | ⟨15, _⟩ => plane439GenDeadBound0015
  | ⟨16, _⟩ => plane439GenDeadBound0016
  | ⟨17, _⟩ => plane439GenDeadBound0017
  | ⟨18, _⟩ => plane439GenDeadBound0018
  | ⟨19, _⟩ => plane439GenDeadBound0019
  | ⟨20, _⟩ => plane439GenDeadBound0020
  | ⟨21, _⟩ => plane439GenDeadBound0021
  | ⟨22, _⟩ => plane439GenDeadBound0022
  | ⟨23, _⟩ => plane439GenDeadBound0023
  | ⟨24, _⟩ => plane439GenDeadBound0024
  | ⟨25, _⟩ => plane439GenDeadBound0025
  | ⟨26, _⟩ => plane439GenDeadBound0026
  | ⟨27, _⟩ => plane439GenDeadBound0027
  | ⟨28, _⟩ => plane439GenDeadBound0028
  | ⟨29, _⟩ => plane439GenDeadBound0029
  | ⟨30, _⟩ => plane439GenDeadBound0030
  | ⟨31, _⟩ => plane439GenDeadBound0031
  | ⟨32, _⟩ => plane439GenDeadBound0032
  | ⟨33, _⟩ => plane439GenDeadBound0033
  | ⟨34, _⟩ => plane439GenDeadBound0034
  | ⟨35, _⟩ => plane439GenDeadBound0035
  | ⟨36, _⟩ => plane439GenDeadBound0036
  | ⟨37, _⟩ => plane439GenDeadBound0037
  | ⟨38, _⟩ => plane439GenDeadBound0038
  | ⟨39, _⟩ => plane439GenDeadBound0039
  | ⟨40, _⟩ => plane439GenDeadBound0040
  | ⟨41, _⟩ => plane439GenDeadBound0041
  | ⟨42, _⟩ => plane439GenDeadBound0042
  | ⟨43, _⟩ => plane439GenDeadBound0043
  | ⟨44, _⟩ => plane439GenDeadBound0044
  | ⟨45, _⟩ => plane439GenDeadBound0045
  | ⟨46, _⟩ => plane439GenDeadBound0046
  | ⟨47, _⟩ => plane439GenDeadBound0047
  | ⟨k + 48, h⟩ => by omega
end QiushiMatmul
