import QiushiPlane456LowerGenBindings00
import QiushiPlane456LowerGenBindings01
import QiushiPlane456LowerGenBindings02
import QiushiPlane456LowerGenBindings03
import QiushiPlane456LowerGenBindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane456LowerGenSourceQRA (i : Fin 50) :
    QuotientRankAtLeast (spanCodes (plane456LowerGenSourceBasis i)) (plane456LowerGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane456LowerGenBound0000
  | ⟨1, _⟩ => plane456LowerGenBound0001
  | ⟨2, _⟩ => plane456LowerGenBound0002
  | ⟨3, _⟩ => plane456LowerGenBound0003
  | ⟨4, _⟩ => plane456LowerGenBound0004
  | ⟨5, _⟩ => plane456LowerGenBound0005
  | ⟨6, _⟩ => plane456LowerGenBound0006
  | ⟨7, _⟩ => plane456LowerGenBound0007
  | ⟨8, _⟩ => plane456LowerGenBound0008
  | ⟨9, _⟩ => plane456LowerGenBound0009
  | ⟨10, _⟩ => plane456LowerGenBound0010
  | ⟨11, _⟩ => plane456LowerGenBound0011
  | ⟨12, _⟩ => plane456LowerGenBound0012
  | ⟨13, _⟩ => plane456LowerGenBound0013
  | ⟨14, _⟩ => plane456LowerGenBound0014
  | ⟨15, _⟩ => plane456LowerGenBound0015
  | ⟨16, _⟩ => plane456LowerGenBound0016
  | ⟨17, _⟩ => plane456LowerGenBound0017
  | ⟨18, _⟩ => plane456LowerGenBound0018
  | ⟨19, _⟩ => plane456LowerGenBound0019
  | ⟨20, _⟩ => plane456LowerGenBound0020
  | ⟨21, _⟩ => plane456LowerGenBound0021
  | ⟨22, _⟩ => plane456LowerGenBound0022
  | ⟨23, _⟩ => plane456LowerGenBound0023
  | ⟨24, _⟩ => plane456LowerGenBound0024
  | ⟨25, _⟩ => plane456LowerGenBound0025
  | ⟨26, _⟩ => plane456LowerGenBound0026
  | ⟨27, _⟩ => plane456LowerGenBound0027
  | ⟨28, _⟩ => plane456LowerGenBound0028
  | ⟨29, _⟩ => plane456LowerGenBound0029
  | ⟨30, _⟩ => plane456LowerGenBound0030
  | ⟨31, _⟩ => plane456LowerGenBound0031
  | ⟨32, _⟩ => plane456LowerGenBound0032
  | ⟨33, _⟩ => plane456LowerGenBound0033
  | ⟨34, _⟩ => plane456LowerGenBound0034
  | ⟨35, _⟩ => plane456LowerGenBound0035
  | ⟨36, _⟩ => plane456LowerGenBound0036
  | ⟨37, _⟩ => plane456LowerGenBound0037
  | ⟨38, _⟩ => plane456LowerGenBound0038
  | ⟨39, _⟩ => plane456LowerGenBound0039
  | ⟨40, _⟩ => plane456LowerGenBound0040
  | ⟨41, _⟩ => plane456LowerGenBound0041
  | ⟨42, _⟩ => plane456LowerGenBound0042
  | ⟨43, _⟩ => plane456LowerGenBound0043
  | ⟨44, _⟩ => plane456LowerGenBound0044
  | ⟨45, _⟩ => plane456LowerGenBound0045
  | ⟨46, _⟩ => plane456LowerGenBound0046
  | ⟨47, _⟩ => plane456LowerGenBound0047
  | ⟨48, _⟩ => plane456LowerGenBound0048
  | ⟨49, _⟩ => plane456LowerGenBound0049
  | ⟨k + 50, h⟩ => by omega
theorem plane456LowerGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (0 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (0 : Fin 49) = [161, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0000 (by decide)
theorem plane456LowerGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (1 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (1 : Fin 49) = [161, 17, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0001 (by decide)
theorem plane456LowerGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (2 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (2 : Fin 49) = [161, 19, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0002 (by decide)
theorem plane456LowerGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (3 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (3 : Fin 49) = [128, 33, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0003 (by decide)
theorem plane456LowerGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (4 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (4 : Fin 49) = [131, 34, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0004 (by decide)
theorem plane456LowerGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (5 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (5 : Fin 49) = [133, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0005 (by decide)
theorem plane456LowerGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (6 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (6 : Fin 49) = [135, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0006 (by decide)
theorem plane456LowerGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (7 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (7 : Fin 49) = [134, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0007 (by decide)
theorem plane456LowerGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (8 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (8 : Fin 49) = [160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0008 (by decide)
theorem plane456LowerGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (9 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (9 : Fin 49) = [160, 70, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0009 (by decide)
theorem plane456LowerGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (10 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (10 : Fin 49) = [132, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0010 (by decide)
theorem plane456LowerGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (11 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (11 : Fin 49) = [132, 71, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0011 (by decide)
theorem plane456LowerGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (12 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (12 : Fin 49) = [130, 64, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0012 (by decide)
theorem plane456LowerGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (13 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (13 : Fin 49) = [130, 71, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0013 (by decide)
theorem plane456LowerGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (14 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (14 : Fin 49) = [132, 64, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0014 (by decide)
theorem plane456LowerGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (15 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (15 : Fin 49) = [129, 69, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0015 (by decide)
theorem plane456LowerGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (16 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (16 : Fin 49) = [130, 69, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0016 (by decide)
theorem plane456LowerGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (17 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (17 : Fin 49) = [161, 103, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0017 (by decide)
theorem plane456LowerGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (18 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (18 : Fin 49) = [257, 161, 19, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0018 (by decide)
theorem plane456LowerGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (19 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (19 : Fin 49) = [262, 160, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0019 (by decide)
theorem plane456LowerGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (20 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (20 : Fin 49) = [257, 130, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0020 (by decide)
theorem plane456LowerGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (21 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (21 : Fin 49) = [258, 129, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0021 (by decide)
theorem plane456LowerGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (22 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (22 : Fin 49) = [256, 130, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0022 (by decide)
theorem plane456LowerGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (23 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (23 : Fin 49) = [256, 132, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0023 (by decide)
theorem plane456LowerGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (24 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (24 : Fin 49) = [259, 132, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0024 (by decide)
theorem plane456LowerGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (25 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (25 : Fin 49) = [261, 130, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0025 (by decide)
theorem plane456LowerGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (26 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (26 : Fin 49) = [295, 161, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0026 (by decide)
theorem plane456LowerGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (27 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (27 : Fin 49) = [320, 161, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0027 (by decide)
theorem plane456LowerGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (28 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (28 : Fin 49) = [256, 161, 65, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0028 (by decide)
theorem plane456LowerGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (29 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (29 : Fin 49) = [258, 161, 67, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0029 (by decide)
theorem plane456LowerGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (30 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (30 : Fin 49) = [260, 161, 69, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0030 (by decide)
theorem plane456LowerGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (31 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (31 : Fin 49) = [289, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0031 (by decide)
theorem plane456LowerGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (32 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (32 : Fin 49) = [292, 161, 101, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0032 (by decide)
theorem plane456LowerGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (33 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (33 : Fin 49) = [260, 161, 70, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0033 (by decide)
theorem plane456LowerGenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (34 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (34 : Fin 49) = [288, 161, 98, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0034 (by decide)
theorem plane456LowerGenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (35 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (35 : Fin 49) = [291, 161, 97, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0035 (by decide)
theorem plane456LowerGenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (36 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (36 : Fin 49) = [257, 161, 66, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0036 (by decide)
theorem plane456LowerGenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (37 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (37 : Fin 49) = [257, 161, 69, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0037 (by decide)
theorem plane456LowerGenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (38 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (38 : Fin 49) = [325, 161, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0038 (by decide)
theorem plane456LowerGenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (39 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (39 : Fin 49) = [256, 161, 70, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0039 (by decide)
theorem plane456LowerGenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (40 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (40 : Fin 49) = [257, 161, 70, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0040 (by decide)
theorem plane456LowerGenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (41 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (41 : Fin 49) = [256, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0041 (by decide)
theorem plane456LowerGenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (42 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (42 : Fin 49) = [258, 161, 99, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0042 (by decide)
theorem plane456LowerGenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (43 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (43 : Fin 49) = [354, 161, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0043 (by decide)
theorem plane456LowerGenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (44 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (44 : Fin 49) = [256, 161, 99, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0044 (by decide)
theorem plane456LowerGenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (45 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (45 : Fin 49) = [256, 161, 100, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0045 (by decide)
theorem plane456LowerGenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (46 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (46 : Fin 49) = [256, 161, 101, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0046 (by decide)
theorem plane456LowerGenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (47 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (47 : Fin 49) = [259, 161, 101, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0047 (by decide)
theorem plane456LowerGenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis (48 : Fin 49))) 16 := by
  rw [show plane456LowerGenDeadBasis (48 : Fin 49) = [359, 161, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane456LowerGenSource0048 (by decide)
theorem plane456LowerGenDeadQRA (d : Fin 49) :
    QuotientRankAtLeast (spanCodes (plane456LowerGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane456LowerGenDeadBound0000
  | ⟨1, _⟩ => plane456LowerGenDeadBound0001
  | ⟨2, _⟩ => plane456LowerGenDeadBound0002
  | ⟨3, _⟩ => plane456LowerGenDeadBound0003
  | ⟨4, _⟩ => plane456LowerGenDeadBound0004
  | ⟨5, _⟩ => plane456LowerGenDeadBound0005
  | ⟨6, _⟩ => plane456LowerGenDeadBound0006
  | ⟨7, _⟩ => plane456LowerGenDeadBound0007
  | ⟨8, _⟩ => plane456LowerGenDeadBound0008
  | ⟨9, _⟩ => plane456LowerGenDeadBound0009
  | ⟨10, _⟩ => plane456LowerGenDeadBound0010
  | ⟨11, _⟩ => plane456LowerGenDeadBound0011
  | ⟨12, _⟩ => plane456LowerGenDeadBound0012
  | ⟨13, _⟩ => plane456LowerGenDeadBound0013
  | ⟨14, _⟩ => plane456LowerGenDeadBound0014
  | ⟨15, _⟩ => plane456LowerGenDeadBound0015
  | ⟨16, _⟩ => plane456LowerGenDeadBound0016
  | ⟨17, _⟩ => plane456LowerGenDeadBound0017
  | ⟨18, _⟩ => plane456LowerGenDeadBound0018
  | ⟨19, _⟩ => plane456LowerGenDeadBound0019
  | ⟨20, _⟩ => plane456LowerGenDeadBound0020
  | ⟨21, _⟩ => plane456LowerGenDeadBound0021
  | ⟨22, _⟩ => plane456LowerGenDeadBound0022
  | ⟨23, _⟩ => plane456LowerGenDeadBound0023
  | ⟨24, _⟩ => plane456LowerGenDeadBound0024
  | ⟨25, _⟩ => plane456LowerGenDeadBound0025
  | ⟨26, _⟩ => plane456LowerGenDeadBound0026
  | ⟨27, _⟩ => plane456LowerGenDeadBound0027
  | ⟨28, _⟩ => plane456LowerGenDeadBound0028
  | ⟨29, _⟩ => plane456LowerGenDeadBound0029
  | ⟨30, _⟩ => plane456LowerGenDeadBound0030
  | ⟨31, _⟩ => plane456LowerGenDeadBound0031
  | ⟨32, _⟩ => plane456LowerGenDeadBound0032
  | ⟨33, _⟩ => plane456LowerGenDeadBound0033
  | ⟨34, _⟩ => plane456LowerGenDeadBound0034
  | ⟨35, _⟩ => plane456LowerGenDeadBound0035
  | ⟨36, _⟩ => plane456LowerGenDeadBound0036
  | ⟨37, _⟩ => plane456LowerGenDeadBound0037
  | ⟨38, _⟩ => plane456LowerGenDeadBound0038
  | ⟨39, _⟩ => plane456LowerGenDeadBound0039
  | ⟨40, _⟩ => plane456LowerGenDeadBound0040
  | ⟨41, _⟩ => plane456LowerGenDeadBound0041
  | ⟨42, _⟩ => plane456LowerGenDeadBound0042
  | ⟨43, _⟩ => plane456LowerGenDeadBound0043
  | ⟨44, _⟩ => plane456LowerGenDeadBound0044
  | ⟨45, _⟩ => plane456LowerGenDeadBound0045
  | ⟨46, _⟩ => plane456LowerGenDeadBound0046
  | ⟨47, _⟩ => plane456LowerGenDeadBound0047
  | ⟨48, _⟩ => plane456LowerGenDeadBound0048
  | ⟨k + 49, h⟩ => by omega
end QiushiMatmul
