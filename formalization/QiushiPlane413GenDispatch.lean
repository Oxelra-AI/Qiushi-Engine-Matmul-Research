import QiushiPlane413GenBindings00
import QiushiPlane413GenBindings01
import QiushiPlane413GenBindings02
import QiushiPlane413GenBindings03
import QiushiPlane413GenBindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane413GenSourceQRA (i : Fin 49) :
    QuotientRankAtLeast (spanCodes (plane413GenSourceBasis i)) (plane413GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane413GenBound0000
  | ⟨1, _⟩ => plane413GenBound0001
  | ⟨2, _⟩ => plane413GenBound0002
  | ⟨3, _⟩ => plane413GenBound0003
  | ⟨4, _⟩ => plane413GenBound0004
  | ⟨5, _⟩ => plane413GenBound0005
  | ⟨6, _⟩ => plane413GenBound0006
  | ⟨7, _⟩ => plane413GenBound0007
  | ⟨8, _⟩ => plane413GenBound0008
  | ⟨9, _⟩ => plane413GenBound0009
  | ⟨10, _⟩ => plane413GenBound0010
  | ⟨11, _⟩ => plane413GenBound0011
  | ⟨12, _⟩ => plane413GenBound0012
  | ⟨13, _⟩ => plane413GenBound0013
  | ⟨14, _⟩ => plane413GenBound0014
  | ⟨15, _⟩ => plane413GenBound0015
  | ⟨16, _⟩ => plane413GenBound0016
  | ⟨17, _⟩ => plane413GenBound0017
  | ⟨18, _⟩ => plane413GenBound0018
  | ⟨19, _⟩ => plane413GenBound0019
  | ⟨20, _⟩ => plane413GenBound0020
  | ⟨21, _⟩ => plane413GenBound0021
  | ⟨22, _⟩ => plane413GenBound0022
  | ⟨23, _⟩ => plane413GenBound0023
  | ⟨24, _⟩ => plane413GenBound0024
  | ⟨25, _⟩ => plane413GenBound0025
  | ⟨26, _⟩ => plane413GenBound0026
  | ⟨27, _⟩ => plane413GenBound0027
  | ⟨28, _⟩ => plane413GenBound0028
  | ⟨29, _⟩ => plane413GenBound0029
  | ⟨30, _⟩ => plane413GenBound0030
  | ⟨31, _⟩ => plane413GenBound0031
  | ⟨32, _⟩ => plane413GenBound0032
  | ⟨33, _⟩ => plane413GenBound0033
  | ⟨34, _⟩ => plane413GenBound0034
  | ⟨35, _⟩ => plane413GenBound0035
  | ⟨36, _⟩ => plane413GenBound0036
  | ⟨37, _⟩ => plane413GenBound0037
  | ⟨38, _⟩ => plane413GenBound0038
  | ⟨39, _⟩ => plane413GenBound0039
  | ⟨40, _⟩ => plane413GenBound0040
  | ⟨41, _⟩ => plane413GenBound0041
  | ⟨42, _⟩ => plane413GenBound0042
  | ⟨43, _⟩ => plane413GenBound0043
  | ⟨44, _⟩ => plane413GenBound0044
  | ⟨45, _⟩ => plane413GenBound0045
  | ⟨46, _⟩ => plane413GenBound0046
  | ⟨47, _⟩ => plane413GenBound0047
  | ⟨48, _⟩ => plane413GenBound0048
  | ⟨k + 49, h⟩ => by omega
theorem plane413GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (0 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (0 : Fin 41) = [68, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0000 (by decide)
theorem plane413GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (1 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (1 : Fin 41) = [76, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0001 (by decide)
theorem plane413GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (2 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (2 : Fin 41) = [132, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0002 (by decide)
theorem plane413GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (3 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (3 : Fin 41) = [148, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0003 (by decide)
theorem plane413GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (4 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (4 : Fin 41) = [196, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0004 (by decide)
theorem plane413GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (5 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (5 : Fin 41) = [220, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0005 (by decide)
theorem plane413GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (6 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (6 : Fin 41) = [32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0006 (by decide)
theorem plane413GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (7 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (7 : Fin 41) = [32, 12, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0007 (by decide)
theorem plane413GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (8 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (8 : Fin 41) = [32, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0008 (by decide)
theorem plane413GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (9 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (9 : Fin 41) = [32, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0009 (by decide)
theorem plane413GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (10 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (10 : Fin 41) = [32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0010 (by decide)
theorem plane413GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (11 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (11 : Fin 41) = [32, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0011 (by decide)
theorem plane413GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (12 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (12 : Fin 41) = [80, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0012 (by decide)
theorem plane413GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (13 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (13 : Fin 41) = [68, 32, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0013 (by decide)
theorem plane413GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (14 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (14 : Fin 41) = [88, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0014 (by decide)
theorem plane413GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (15 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (15 : Fin 41) = [68, 32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0015 (by decide)
theorem plane413GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (16 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (16 : Fin 41) = [136, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0016 (by decide)
theorem plane413GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (17 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (17 : Fin 41) = [132, 32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0017 (by decide)
theorem plane413GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (18 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (18 : Fin 41) = [152, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0018 (by decide)
theorem plane413GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (19 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (19 : Fin 41) = [132, 32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0019 (by decide)
theorem plane413GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (20 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (20 : Fin 41) = [200, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0020 (by decide)
theorem plane413GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (21 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (21 : Fin 41) = [136, 68, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0021 (by decide)
theorem plane413GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (22 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (22 : Fin 41) = [208, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0022 (by decide)
theorem plane413GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (23 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (23 : Fin 41) = [132, 80, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0023 (by decide)
theorem plane413GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (24 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (24 : Fin 41) = [264, 32, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0024 (by decide)
theorem plane413GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (25 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (25 : Fin 41) = [268, 32, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0025 (by decide)
theorem plane413GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (26 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (26 : Fin 41) = [264, 32, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0026 (by decide)
theorem plane413GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (27 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (27 : Fin 41) = [264, 32, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0027 (by decide)
theorem plane413GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (28 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (28 : Fin 41) = [264, 32, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0028 (by decide)
theorem plane413GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (29 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (29 : Fin 41) = [336, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0029 (by decide)
theorem plane413GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (30 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (30 : Fin 41) = [340, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0030 (by decide)
theorem plane413GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (31 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (31 : Fin 41) = [344, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0031 (by decide)
theorem plane413GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (32 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (32 : Fin 41) = [348, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0032 (by decide)
theorem plane413GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (33 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (33 : Fin 41) = [392, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0033 (by decide)
theorem plane413GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (34 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (34 : Fin 41) = [396, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0034 (by decide)
theorem plane413GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (35 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (35 : Fin 41) = [408, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0035 (by decide)
theorem plane413GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (36 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (36 : Fin 41) = [412, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0036 (by decide)
theorem plane413GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (37 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (37 : Fin 41) = [456, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0037 (by decide)
theorem plane413GenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (38 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (38 : Fin 41) = [460, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0038 (by decide)
theorem plane413GenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (39 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (39 : Fin 41) = [464, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0039 (by decide)
theorem plane413GenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis (40 : Fin 41))) 15 := by
  rw [show plane413GenDeadBasis (40 : Fin 41) = [468, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane413GenSource0040 (by decide)
theorem plane413GenDeadQRA (d : Fin 41) :
    QuotientRankAtLeast (spanCodes (plane413GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane413GenDeadBound0000
  | ⟨1, _⟩ => plane413GenDeadBound0001
  | ⟨2, _⟩ => plane413GenDeadBound0002
  | ⟨3, _⟩ => plane413GenDeadBound0003
  | ⟨4, _⟩ => plane413GenDeadBound0004
  | ⟨5, _⟩ => plane413GenDeadBound0005
  | ⟨6, _⟩ => plane413GenDeadBound0006
  | ⟨7, _⟩ => plane413GenDeadBound0007
  | ⟨8, _⟩ => plane413GenDeadBound0008
  | ⟨9, _⟩ => plane413GenDeadBound0009
  | ⟨10, _⟩ => plane413GenDeadBound0010
  | ⟨11, _⟩ => plane413GenDeadBound0011
  | ⟨12, _⟩ => plane413GenDeadBound0012
  | ⟨13, _⟩ => plane413GenDeadBound0013
  | ⟨14, _⟩ => plane413GenDeadBound0014
  | ⟨15, _⟩ => plane413GenDeadBound0015
  | ⟨16, _⟩ => plane413GenDeadBound0016
  | ⟨17, _⟩ => plane413GenDeadBound0017
  | ⟨18, _⟩ => plane413GenDeadBound0018
  | ⟨19, _⟩ => plane413GenDeadBound0019
  | ⟨20, _⟩ => plane413GenDeadBound0020
  | ⟨21, _⟩ => plane413GenDeadBound0021
  | ⟨22, _⟩ => plane413GenDeadBound0022
  | ⟨23, _⟩ => plane413GenDeadBound0023
  | ⟨24, _⟩ => plane413GenDeadBound0024
  | ⟨25, _⟩ => plane413GenDeadBound0025
  | ⟨26, _⟩ => plane413GenDeadBound0026
  | ⟨27, _⟩ => plane413GenDeadBound0027
  | ⟨28, _⟩ => plane413GenDeadBound0028
  | ⟨29, _⟩ => plane413GenDeadBound0029
  | ⟨30, _⟩ => plane413GenDeadBound0030
  | ⟨31, _⟩ => plane413GenDeadBound0031
  | ⟨32, _⟩ => plane413GenDeadBound0032
  | ⟨33, _⟩ => plane413GenDeadBound0033
  | ⟨34, _⟩ => plane413GenDeadBound0034
  | ⟨35, _⟩ => plane413GenDeadBound0035
  | ⟨36, _⟩ => plane413GenDeadBound0036
  | ⟨37, _⟩ => plane413GenDeadBound0037
  | ⟨38, _⟩ => plane413GenDeadBound0038
  | ⟨39, _⟩ => plane413GenDeadBound0039
  | ⟨40, _⟩ => plane413GenDeadBound0040
  | ⟨k + 41, h⟩ => by omega
end QiushiMatmul
