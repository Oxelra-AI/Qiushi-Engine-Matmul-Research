import QiushiPlane459GenBindings00
import QiushiPlane459GenBindings01
import QiushiPlane459GenBindings02
import QiushiPlane459GenBindings03
import QiushiPlane459GenBindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane459GenSourceQRA (i : Fin 42) :
    QuotientRankAtLeast (spanCodes (plane459GenSourceBasis i)) (plane459GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane459GenBound0000
  | ⟨1, _⟩ => plane459GenBound0001
  | ⟨2, _⟩ => plane459GenBound0002
  | ⟨3, _⟩ => plane459GenBound0003
  | ⟨4, _⟩ => plane459GenBound0004
  | ⟨5, _⟩ => plane459GenBound0005
  | ⟨6, _⟩ => plane459GenBound0006
  | ⟨7, _⟩ => plane459GenBound0007
  | ⟨8, _⟩ => plane459GenBound0008
  | ⟨9, _⟩ => plane459GenBound0009
  | ⟨10, _⟩ => plane459GenBound0010
  | ⟨11, _⟩ => plane459GenBound0011
  | ⟨12, _⟩ => plane459GenBound0012
  | ⟨13, _⟩ => plane459GenBound0013
  | ⟨14, _⟩ => plane459GenBound0014
  | ⟨15, _⟩ => plane459GenBound0015
  | ⟨16, _⟩ => plane459GenBound0016
  | ⟨17, _⟩ => plane459GenBound0017
  | ⟨18, _⟩ => plane459GenBound0018
  | ⟨19, _⟩ => plane459GenBound0019
  | ⟨20, _⟩ => plane459GenBound0020
  | ⟨21, _⟩ => plane459GenBound0021
  | ⟨22, _⟩ => plane459GenBound0022
  | ⟨23, _⟩ => plane459GenBound0023
  | ⟨24, _⟩ => plane459GenBound0024
  | ⟨25, _⟩ => plane459GenBound0025
  | ⟨26, _⟩ => plane459GenBound0026
  | ⟨27, _⟩ => plane459GenBound0027
  | ⟨28, _⟩ => plane459GenBound0028
  | ⟨29, _⟩ => plane459GenBound0029
  | ⟨30, _⟩ => plane459GenBound0030
  | ⟨31, _⟩ => plane459GenBound0031
  | ⟨32, _⟩ => plane459GenBound0032
  | ⟨33, _⟩ => plane459GenBound0033
  | ⟨34, _⟩ => plane459GenBound0034
  | ⟨35, _⟩ => plane459GenBound0035
  | ⟨36, _⟩ => plane459GenBound0036
  | ⟨37, _⟩ => plane459GenBound0037
  | ⟨38, _⟩ => plane459GenBound0038
  | ⟨39, _⟩ => plane459GenBound0039
  | ⟨40, _⟩ => plane459GenBound0040
  | ⟨41, _⟩ => plane459GenBound0041
  | ⟨k + 42, h⟩ => by omega
theorem plane459GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (0 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (0 : Fin 35) = [160, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0000 (by decide)
theorem plane459GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (1 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (1 : Fin 35) = [160, 68, 16, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0001 (by decide)
theorem plane459GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (2 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (2 : Fin 35) = [160, 68, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0002 (by decide)
theorem plane459GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (3 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (3 : Fin 35) = [160, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0003 (by decide)
theorem plane459GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (4 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (4 : Fin 35) = [160, 68, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0004 (by decide)
theorem plane459GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (5 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (5 : Fin 35) = [160, 68, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0005 (by decide)
theorem plane459GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (6 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (6 : Fin 35) = [160, 68, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0006 (by decide)
theorem plane459GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (7 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (7 : Fin 35) = [129, 68, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0007 (by decide)
theorem plane459GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (8 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (8 : Fin 35) = [131, 68, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0008 (by decide)
theorem plane459GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (9 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (9 : Fin 35) = [133, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0009 (by decide)
theorem plane459GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (10 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (10 : Fin 35) = [134, 68, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0010 (by decide)
theorem plane459GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (11 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (11 : Fin 35) = [145, 68, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0011 (by decide)
theorem plane459GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (12 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (12 : Fin 35) = [147, 68, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0012 (by decide)
theorem plane459GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (13 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (13 : Fin 35) = [148, 68, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0013 (by decide)
theorem plane459GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (14 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (14 : Fin 35) = [151, 68, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0014 (by decide)
theorem plane459GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (15 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (15 : Fin 35) = [256, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0015 (by decide)
theorem plane459GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (16 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (16 : Fin 35) = [257, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0016 (by decide)
theorem plane459GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (17 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (17 : Fin 35) = [258, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0017 (by decide)
theorem plane459GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (18 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (18 : Fin 35) = [259, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0018 (by decide)
theorem plane459GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (19 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (19 : Fin 35) = [262, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0019 (by decide)
theorem plane459GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (20 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (20 : Fin 35) = [263, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0020 (by decide)
theorem plane459GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (21 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (21 : Fin 35) = [272, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0021 (by decide)
theorem plane459GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (22 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (22 : Fin 35) = [273, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0022 (by decide)
theorem plane459GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (23 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (23 : Fin 35) = [274, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0023 (by decide)
theorem plane459GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (24 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (24 : Fin 35) = [275, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0024 (by decide)
theorem plane459GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (25 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (25 : Fin 35) = [276, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0025 (by decide)
theorem plane459GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (26 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (26 : Fin 35) = [277, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0026 (by decide)
theorem plane459GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (27 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (27 : Fin 35) = [289, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0027 (by decide)
theorem plane459GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (28 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (28 : Fin 35) = [290, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0028 (by decide)
theorem plane459GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (29 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (29 : Fin 35) = [293, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0029 (by decide)
theorem plane459GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (30 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (30 : Fin 35) = [295, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0030 (by decide)
theorem plane459GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (31 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (31 : Fin 35) = [305, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0031 (by decide)
theorem plane459GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (32 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (32 : Fin 35) = [306, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0032 (by decide)
theorem plane459GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (33 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (33 : Fin 35) = [308, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0033 (by decide)
theorem plane459GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis (34 : Fin 35))) 17 := by
  rw [show plane459GenDeadBasis (34 : Fin 35) = [310, 160, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane459GenSource0034 (by decide)
theorem plane459GenDeadQRA (d : Fin 35) :
    QuotientRankAtLeast (spanCodes (plane459GenDeadBasis d)) 17 :=
  match d with
  | ⟨0, _⟩ => plane459GenDeadBound0000
  | ⟨1, _⟩ => plane459GenDeadBound0001
  | ⟨2, _⟩ => plane459GenDeadBound0002
  | ⟨3, _⟩ => plane459GenDeadBound0003
  | ⟨4, _⟩ => plane459GenDeadBound0004
  | ⟨5, _⟩ => plane459GenDeadBound0005
  | ⟨6, _⟩ => plane459GenDeadBound0006
  | ⟨7, _⟩ => plane459GenDeadBound0007
  | ⟨8, _⟩ => plane459GenDeadBound0008
  | ⟨9, _⟩ => plane459GenDeadBound0009
  | ⟨10, _⟩ => plane459GenDeadBound0010
  | ⟨11, _⟩ => plane459GenDeadBound0011
  | ⟨12, _⟩ => plane459GenDeadBound0012
  | ⟨13, _⟩ => plane459GenDeadBound0013
  | ⟨14, _⟩ => plane459GenDeadBound0014
  | ⟨15, _⟩ => plane459GenDeadBound0015
  | ⟨16, _⟩ => plane459GenDeadBound0016
  | ⟨17, _⟩ => plane459GenDeadBound0017
  | ⟨18, _⟩ => plane459GenDeadBound0018
  | ⟨19, _⟩ => plane459GenDeadBound0019
  | ⟨20, _⟩ => plane459GenDeadBound0020
  | ⟨21, _⟩ => plane459GenDeadBound0021
  | ⟨22, _⟩ => plane459GenDeadBound0022
  | ⟨23, _⟩ => plane459GenDeadBound0023
  | ⟨24, _⟩ => plane459GenDeadBound0024
  | ⟨25, _⟩ => plane459GenDeadBound0025
  | ⟨26, _⟩ => plane459GenDeadBound0026
  | ⟨27, _⟩ => plane459GenDeadBound0027
  | ⟨28, _⟩ => plane459GenDeadBound0028
  | ⟨29, _⟩ => plane459GenDeadBound0029
  | ⟨30, _⟩ => plane459GenDeadBound0030
  | ⟨31, _⟩ => plane459GenDeadBound0031
  | ⟨32, _⟩ => plane459GenDeadBound0032
  | ⟨33, _⟩ => plane459GenDeadBound0033
  | ⟨34, _⟩ => plane459GenDeadBound0034
  | ⟨k + 35, h⟩ => by omega
end QiushiMatmul
