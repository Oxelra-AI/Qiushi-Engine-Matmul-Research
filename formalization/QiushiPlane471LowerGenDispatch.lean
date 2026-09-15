import QiushiPlane471LowerGenBindings00
import QiushiPlane471LowerGenBindings01
import QiushiPlane471LowerGenBindings02
import QiushiPlane471LowerGenBindings03
import QiushiPlane471LowerGenBindings04
import QiushiPlane471LowerGenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane471LowerGenSourceQRA (i : Fin 53) :
    QuotientRankAtLeast (spanCodes (plane471LowerGenSourceBasis i)) (plane471LowerGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane471LowerGenBound0000
  | ⟨1, _⟩ => plane471LowerGenBound0001
  | ⟨2, _⟩ => plane471LowerGenBound0002
  | ⟨3, _⟩ => plane471LowerGenBound0003
  | ⟨4, _⟩ => plane471LowerGenBound0004
  | ⟨5, _⟩ => plane471LowerGenBound0005
  | ⟨6, _⟩ => plane471LowerGenBound0006
  | ⟨7, _⟩ => plane471LowerGenBound0007
  | ⟨8, _⟩ => plane471LowerGenBound0008
  | ⟨9, _⟩ => plane471LowerGenBound0009
  | ⟨10, _⟩ => plane471LowerGenBound0010
  | ⟨11, _⟩ => plane471LowerGenBound0011
  | ⟨12, _⟩ => plane471LowerGenBound0012
  | ⟨13, _⟩ => plane471LowerGenBound0013
  | ⟨14, _⟩ => plane471LowerGenBound0014
  | ⟨15, _⟩ => plane471LowerGenBound0015
  | ⟨16, _⟩ => plane471LowerGenBound0016
  | ⟨17, _⟩ => plane471LowerGenBound0017
  | ⟨18, _⟩ => plane471LowerGenBound0018
  | ⟨19, _⟩ => plane471LowerGenBound0019
  | ⟨20, _⟩ => plane471LowerGenBound0020
  | ⟨21, _⟩ => plane471LowerGenBound0021
  | ⟨22, _⟩ => plane471LowerGenBound0022
  | ⟨23, _⟩ => plane471LowerGenBound0023
  | ⟨24, _⟩ => plane471LowerGenBound0024
  | ⟨25, _⟩ => plane471LowerGenBound0025
  | ⟨26, _⟩ => plane471LowerGenBound0026
  | ⟨27, _⟩ => plane471LowerGenBound0027
  | ⟨28, _⟩ => plane471LowerGenBound0028
  | ⟨29, _⟩ => plane471LowerGenBound0029
  | ⟨30, _⟩ => plane471LowerGenBound0030
  | ⟨31, _⟩ => plane471LowerGenBound0031
  | ⟨32, _⟩ => plane471LowerGenBound0032
  | ⟨33, _⟩ => plane471LowerGenBound0033
  | ⟨34, _⟩ => plane471LowerGenBound0034
  | ⟨35, _⟩ => plane471LowerGenBound0035
  | ⟨36, _⟩ => plane471LowerGenBound0036
  | ⟨37, _⟩ => plane471LowerGenBound0037
  | ⟨38, _⟩ => plane471LowerGenBound0038
  | ⟨39, _⟩ => plane471LowerGenBound0039
  | ⟨40, _⟩ => plane471LowerGenBound0040
  | ⟨41, _⟩ => plane471LowerGenBound0041
  | ⟨42, _⟩ => plane471LowerGenBound0042
  | ⟨43, _⟩ => plane471LowerGenBound0043
  | ⟨44, _⟩ => plane471LowerGenBound0044
  | ⟨45, _⟩ => plane471LowerGenBound0045
  | ⟨46, _⟩ => plane471LowerGenBound0046
  | ⟨47, _⟩ => plane471LowerGenBound0047
  | ⟨48, _⟩ => plane471LowerGenBound0048
  | ⟨49, _⟩ => plane471LowerGenBound0049
  | ⟨50, _⟩ => plane471LowerGenBound0050
  | ⟨51, _⟩ => plane471LowerGenBound0051
  | ⟨52, _⟩ => plane471LowerGenBound0052
  | ⟨k + 53, h⟩ => by omega
theorem plane471LowerGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (0 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (0 : Fin 49) = [289, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0000 (by decide)
theorem plane471LowerGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (1 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (1 : Fin 49) = [289, 66, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0001 (by decide)
theorem plane471LowerGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (2 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (2 : Fin 49) = [259, 80, 34, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0002 (by decide)
theorem plane471LowerGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (3 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (3 : Fin 49) = [258, 80, 35, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0003 (by decide)
theorem plane471LowerGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (4 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (4 : Fin 49) = [273, 84, 48, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0004 (by decide)
theorem plane471LowerGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (5 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (5 : Fin 49) = [257, 69, 32, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0005 (by decide)
theorem plane471LowerGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (6 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (6 : Fin 49) = [259, 71, 34, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0006 (by decide)
theorem plane471LowerGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (7 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (7 : Fin 49) = [261, 65, 36, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0007 (by decide)
theorem plane471LowerGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (8 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (8 : Fin 49) = [260, 64, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0008 (by decide)
theorem plane471LowerGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (9 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (9 : Fin 49) = [257, 71, 32, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0009 (by decide)
theorem plane471LowerGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (10 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (10 : Fin 49) = [258, 68, 35, 16, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0010 (by decide)
theorem plane471LowerGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (11 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (11 : Fin 49) = [257, 64, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0011 (by decide)
theorem plane471LowerGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (12 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (12 : Fin 49) = [256, 65, 33, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0012 (by decide)
theorem plane471LowerGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (13 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (13 : Fin 49) = [274, 83, 51, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0013 (by decide)
theorem plane471LowerGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (14 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (14 : Fin 49) = [276, 84, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0014 (by decide)
theorem plane471LowerGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (15 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (15 : Fin 49) = [256, 66, 33, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0015 (by decide)
theorem plane471LowerGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (16 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (16 : Fin 49) = [272, 82, 49, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0016 (by decide)
theorem plane471LowerGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (17 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (17 : Fin 49) = [289, 128, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0017 (by decide)
theorem plane471LowerGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (18 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (18 : Fin 49) = [289, 131, 83, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0018 (by decide)
theorem plane471LowerGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (19 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (19 : Fin 49) = [289, 129, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0019 (by decide)
theorem plane471LowerGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (20 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (20 : Fin 49) = [289, 129, 83, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0020 (by decide)
theorem plane471LowerGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (21 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (21 : Fin 49) = [289, 129, 82, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0021 (by decide)
theorem plane471LowerGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (22 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (22 : Fin 49) = [289, 129, 69, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0022 (by decide)
theorem plane471LowerGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (23 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (23 : Fin 49) = [289, 129, 71, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0023 (by decide)
theorem plane471LowerGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (24 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (24 : Fin 49) = [289, 131, 68, 16, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0024 (by decide)
theorem plane471LowerGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (25 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (25 : Fin 49) = [289, 129, 64, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0025 (by decide)
theorem plane471LowerGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (26 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (26 : Fin 49) = [289, 145, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0026 (by decide)
theorem plane471LowerGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (27 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (27 : Fin 49) = [289, 131, 65, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0027 (by decide)
theorem plane471LowerGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (28 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (28 : Fin 49) = [289, 151, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0028 (by decide)
theorem plane471LowerGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (29 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (29 : Fin 49) = [258, 131, 84, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0029 (by decide)
theorem plane471LowerGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (30 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (30 : Fin 49) = [277, 148, 84, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0030 (by decide)
theorem plane471LowerGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (31 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (31 : Fin 49) = [279, 150, 84, 54, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0031 (by decide)
theorem plane471LowerGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (32 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (32 : Fin 49) = [259, 131, 84, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0032 (by decide)
theorem plane471LowerGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (33 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (33 : Fin 49) = [258, 129, 84, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0033 (by decide)
theorem plane471LowerGenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (34 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (34 : Fin 49) = [259, 129, 84, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0034 (by decide)
theorem plane471LowerGenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (35 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (35 : Fin 49) = [260, 129, 84, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0035 (by decide)
theorem plane471LowerGenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (36 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (36 : Fin 49) = [263, 130, 84, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0036 (by decide)
theorem plane471LowerGenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (37 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (37 : Fin 49) = [275, 150, 84, 50, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0037 (by decide)
theorem plane471LowerGenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (38 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (38 : Fin 49) = [261, 129, 84, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0038 (by decide)
theorem plane471LowerGenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (39 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (39 : Fin 49) = [262, 129, 84, 39, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0039 (by decide)
theorem plane471LowerGenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (40 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (40 : Fin 49) = [289, 167, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0040 (by decide)
theorem plane471LowerGenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (41 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (41 : Fin 49) = [272, 129, 84, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0041 (by decide)
theorem plane471LowerGenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (42 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (42 : Fin 49) = [272, 128, 84, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0042 (by decide)
theorem plane471LowerGenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (43 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (43 : Fin 49) = [274, 129, 84, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0043 (by decide)
theorem plane471LowerGenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (44 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (44 : Fin 49) = [275, 129, 84, 50, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0044 (by decide)
theorem plane471LowerGenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (45 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (45 : Fin 49) = [278, 131, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0045 (by decide)
theorem plane471LowerGenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (46 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (46 : Fin 49) = [289, 181, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0046 (by decide)
theorem plane471LowerGenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (47 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (47 : Fin 49) = [278, 129, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0047 (by decide)
theorem plane471LowerGenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis (48 : Fin 49))) 16 := by
  rw [show plane471LowerGenDeadBasis (48 : Fin 49) = [278, 128, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane471LowerGenSource0048 (by decide)
theorem plane471LowerGenDeadQRA (d : Fin 49) :
    QuotientRankAtLeast (spanCodes (plane471LowerGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane471LowerGenDeadBound0000
  | ⟨1, _⟩ => plane471LowerGenDeadBound0001
  | ⟨2, _⟩ => plane471LowerGenDeadBound0002
  | ⟨3, _⟩ => plane471LowerGenDeadBound0003
  | ⟨4, _⟩ => plane471LowerGenDeadBound0004
  | ⟨5, _⟩ => plane471LowerGenDeadBound0005
  | ⟨6, _⟩ => plane471LowerGenDeadBound0006
  | ⟨7, _⟩ => plane471LowerGenDeadBound0007
  | ⟨8, _⟩ => plane471LowerGenDeadBound0008
  | ⟨9, _⟩ => plane471LowerGenDeadBound0009
  | ⟨10, _⟩ => plane471LowerGenDeadBound0010
  | ⟨11, _⟩ => plane471LowerGenDeadBound0011
  | ⟨12, _⟩ => plane471LowerGenDeadBound0012
  | ⟨13, _⟩ => plane471LowerGenDeadBound0013
  | ⟨14, _⟩ => plane471LowerGenDeadBound0014
  | ⟨15, _⟩ => plane471LowerGenDeadBound0015
  | ⟨16, _⟩ => plane471LowerGenDeadBound0016
  | ⟨17, _⟩ => plane471LowerGenDeadBound0017
  | ⟨18, _⟩ => plane471LowerGenDeadBound0018
  | ⟨19, _⟩ => plane471LowerGenDeadBound0019
  | ⟨20, _⟩ => plane471LowerGenDeadBound0020
  | ⟨21, _⟩ => plane471LowerGenDeadBound0021
  | ⟨22, _⟩ => plane471LowerGenDeadBound0022
  | ⟨23, _⟩ => plane471LowerGenDeadBound0023
  | ⟨24, _⟩ => plane471LowerGenDeadBound0024
  | ⟨25, _⟩ => plane471LowerGenDeadBound0025
  | ⟨26, _⟩ => plane471LowerGenDeadBound0026
  | ⟨27, _⟩ => plane471LowerGenDeadBound0027
  | ⟨28, _⟩ => plane471LowerGenDeadBound0028
  | ⟨29, _⟩ => plane471LowerGenDeadBound0029
  | ⟨30, _⟩ => plane471LowerGenDeadBound0030
  | ⟨31, _⟩ => plane471LowerGenDeadBound0031
  | ⟨32, _⟩ => plane471LowerGenDeadBound0032
  | ⟨33, _⟩ => plane471LowerGenDeadBound0033
  | ⟨34, _⟩ => plane471LowerGenDeadBound0034
  | ⟨35, _⟩ => plane471LowerGenDeadBound0035
  | ⟨36, _⟩ => plane471LowerGenDeadBound0036
  | ⟨37, _⟩ => plane471LowerGenDeadBound0037
  | ⟨38, _⟩ => plane471LowerGenDeadBound0038
  | ⟨39, _⟩ => plane471LowerGenDeadBound0039
  | ⟨40, _⟩ => plane471LowerGenDeadBound0040
  | ⟨41, _⟩ => plane471LowerGenDeadBound0041
  | ⟨42, _⟩ => plane471LowerGenDeadBound0042
  | ⟨43, _⟩ => plane471LowerGenDeadBound0043
  | ⟨44, _⟩ => plane471LowerGenDeadBound0044
  | ⟨45, _⟩ => plane471LowerGenDeadBound0045
  | ⟨46, _⟩ => plane471LowerGenDeadBound0046
  | ⟨47, _⟩ => plane471LowerGenDeadBound0047
  | ⟨48, _⟩ => plane471LowerGenDeadBound0048
  | ⟨k + 49, h⟩ => by omega
end QiushiMatmul
