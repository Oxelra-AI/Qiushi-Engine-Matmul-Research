import QiushiPlane470LowerGenBindings00
import QiushiPlane470LowerGenBindings01
import QiushiPlane470LowerGenBindings02
import QiushiPlane470LowerGenBindings03
import QiushiPlane470LowerGenBindings04
import QiushiPlane470LowerGenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane470LowerGenSourceQRA (i : Fin 52) :
    QuotientRankAtLeast (spanCodes (plane470LowerGenSourceBasis i)) (plane470LowerGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane470LowerGenBound0000
  | ⟨1, _⟩ => plane470LowerGenBound0001
  | ⟨2, _⟩ => plane470LowerGenBound0002
  | ⟨3, _⟩ => plane470LowerGenBound0003
  | ⟨4, _⟩ => plane470LowerGenBound0004
  | ⟨5, _⟩ => plane470LowerGenBound0005
  | ⟨6, _⟩ => plane470LowerGenBound0006
  | ⟨7, _⟩ => plane470LowerGenBound0007
  | ⟨8, _⟩ => plane470LowerGenBound0008
  | ⟨9, _⟩ => plane470LowerGenBound0009
  | ⟨10, _⟩ => plane470LowerGenBound0010
  | ⟨11, _⟩ => plane470LowerGenBound0011
  | ⟨12, _⟩ => plane470LowerGenBound0012
  | ⟨13, _⟩ => plane470LowerGenBound0013
  | ⟨14, _⟩ => plane470LowerGenBound0014
  | ⟨15, _⟩ => plane470LowerGenBound0015
  | ⟨16, _⟩ => plane470LowerGenBound0016
  | ⟨17, _⟩ => plane470LowerGenBound0017
  | ⟨18, _⟩ => plane470LowerGenBound0018
  | ⟨19, _⟩ => plane470LowerGenBound0019
  | ⟨20, _⟩ => plane470LowerGenBound0020
  | ⟨21, _⟩ => plane470LowerGenBound0021
  | ⟨22, _⟩ => plane470LowerGenBound0022
  | ⟨23, _⟩ => plane470LowerGenBound0023
  | ⟨24, _⟩ => plane470LowerGenBound0024
  | ⟨25, _⟩ => plane470LowerGenBound0025
  | ⟨26, _⟩ => plane470LowerGenBound0026
  | ⟨27, _⟩ => plane470LowerGenBound0027
  | ⟨28, _⟩ => plane470LowerGenBound0028
  | ⟨29, _⟩ => plane470LowerGenBound0029
  | ⟨30, _⟩ => plane470LowerGenBound0030
  | ⟨31, _⟩ => plane470LowerGenBound0031
  | ⟨32, _⟩ => plane470LowerGenBound0032
  | ⟨33, _⟩ => plane470LowerGenBound0033
  | ⟨34, _⟩ => plane470LowerGenBound0034
  | ⟨35, _⟩ => plane470LowerGenBound0035
  | ⟨36, _⟩ => plane470LowerGenBound0036
  | ⟨37, _⟩ => plane470LowerGenBound0037
  | ⟨38, _⟩ => plane470LowerGenBound0038
  | ⟨39, _⟩ => plane470LowerGenBound0039
  | ⟨40, _⟩ => plane470LowerGenBound0040
  | ⟨41, _⟩ => plane470LowerGenBound0041
  | ⟨42, _⟩ => plane470LowerGenBound0042
  | ⟨43, _⟩ => plane470LowerGenBound0043
  | ⟨44, _⟩ => plane470LowerGenBound0044
  | ⟨45, _⟩ => plane470LowerGenBound0045
  | ⟨46, _⟩ => plane470LowerGenBound0046
  | ⟨47, _⟩ => plane470LowerGenBound0047
  | ⟨48, _⟩ => plane470LowerGenBound0048
  | ⟨49, _⟩ => plane470LowerGenBound0049
  | ⟨50, _⟩ => plane470LowerGenBound0050
  | ⟨51, _⟩ => plane470LowerGenBound0051
  | ⟨k + 52, h⟩ => by omega
theorem plane470LowerGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (0 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (0 : Fin 50) = [259, 83, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0000 (by decide)
theorem plane470LowerGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (1 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (1 : Fin 50) = [258, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0001 (by decide)
theorem plane470LowerGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (2 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (2 : Fin 50) = [259, 67, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0002 (by decide)
theorem plane470LowerGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (3 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (3 : Fin 50) = [259, 80, 33, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0003 (by decide)
theorem plane470LowerGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (4 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (4 : Fin 50) = [259, 80, 34, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0004 (by decide)
theorem plane470LowerGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (5 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (5 : Fin 50) = [259, 84, 39, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0005 (by decide)
theorem plane470LowerGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (6 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (6 : Fin 50) = [259, 84, 48, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0006 (by decide)
theorem plane470LowerGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (7 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (7 : Fin 50) = [259, 69, 32, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0007 (by decide)
theorem plane470LowerGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (8 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (8 : Fin 50) = [259, 71, 34, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0008 (by decide)
theorem plane470LowerGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (9 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (9 : Fin 50) = [259, 65, 36, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0009 (by decide)
theorem plane470LowerGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (10 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (10 : Fin 50) = [259, 64, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0010 (by decide)
theorem plane470LowerGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (11 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (11 : Fin 50) = [259, 71, 33, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0011 (by decide)
theorem plane470LowerGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (12 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (12 : Fin 50) = [259, 71, 32, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0012 (by decide)
theorem plane470LowerGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (13 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (13 : Fin 50) = [259, 66, 37, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0013 (by decide)
theorem plane470LowerGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (14 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (14 : Fin 50) = [259, 64, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0014 (by decide)
theorem plane470LowerGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (15 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (15 : Fin 50) = [259, 81, 49, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0015 (by decide)
theorem plane470LowerGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (16 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (16 : Fin 50) = [259, 82, 50, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0016 (by decide)
theorem plane470LowerGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (17 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (17 : Fin 50) = [259, 71, 37, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0017 (by decide)
theorem plane470LowerGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (18 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (18 : Fin 50) = [259, 66, 33, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0018 (by decide)
theorem plane470LowerGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (19 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (19 : Fin 50) = [259, 64, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0019 (by decide)
theorem plane470LowerGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (20 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (20 : Fin 50) = [259, 128, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0020 (by decide)
theorem plane470LowerGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (21 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (21 : Fin 50) = [259, 129, 81, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0021 (by decide)
theorem plane470LowerGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (22 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (22 : Fin 50) = [259, 130, 82, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0022 (by decide)
theorem plane470LowerGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (23 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (23 : Fin 50) = [259, 129, 82, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0023 (by decide)
theorem plane470LowerGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (24 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (24 : Fin 50) = [259, 131, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0024 (by decide)
theorem plane470LowerGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (25 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (25 : Fin 50) = [259, 144, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0025 (by decide)
theorem plane470LowerGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (26 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (26 : Fin 50) = [259, 128, 69, 17, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0026 (by decide)
theorem plane470LowerGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (27 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (27 : Fin 50) = [259, 129, 71, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0027 (by decide)
theorem plane470LowerGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (28 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (28 : Fin 50) = [259, 128, 71, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0028 (by decide)
theorem plane470LowerGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (29 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (29 : Fin 50) = [259, 134, 65, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0029 (by decide)
theorem plane470LowerGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (30 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (30 : Fin 50) = [259, 132, 68, 16, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0030 (by decide)
theorem plane470LowerGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (31 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (31 : Fin 50) = [259, 129, 64, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0031 (by decide)
theorem plane470LowerGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (32 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (32 : Fin 50) = [259, 130, 64, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0032 (by decide)
theorem plane470LowerGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (33 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (33 : Fin 50) = [259, 151, 84, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0033 (by decide)
theorem plane470LowerGenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (34 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (34 : Fin 50) = [259, 129, 84, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0034 (by decide)
theorem plane470LowerGenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (35 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (35 : Fin 50) = [259, 128, 84, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0035 (by decide)
theorem plane470LowerGenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (36 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (36 : Fin 50) = [259, 132, 84, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0036 (by decide)
theorem plane470LowerGenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (37 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (37 : Fin 50) = [259, 129, 84, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0037 (by decide)
theorem plane470LowerGenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (38 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (38 : Fin 50) = [259, 128, 84, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0038 (by decide)
theorem plane470LowerGenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (39 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (39 : Fin 50) = [259, 129, 84, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0039 (by decide)
theorem plane470LowerGenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (40 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (40 : Fin 50) = [259, 128, 84, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0040 (by decide)
theorem plane470LowerGenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (41 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (41 : Fin 50) = [259, 129, 84, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0041 (by decide)
theorem plane470LowerGenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (42 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (42 : Fin 50) = [259, 129, 84, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0042 (by decide)
theorem plane470LowerGenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (43 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (43 : Fin 50) = [259, 128, 84, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0043 (by decide)
theorem plane470LowerGenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (44 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (44 : Fin 50) = [259, 129, 84, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0044 (by decide)
theorem plane470LowerGenDeadBound0045 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (45 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (45 : Fin 50) = [259, 132, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0045 (by decide)
theorem plane470LowerGenDeadBound0046 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (46 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (46 : Fin 50) = [259, 128, 84, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0046 (by decide)
theorem plane470LowerGenDeadBound0047 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (47 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (47 : Fin 50) = [259, 129, 84, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0047 (by decide)
theorem plane470LowerGenDeadBound0048 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (48 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (48 : Fin 50) = [259, 129, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0048 (by decide)
theorem plane470LowerGenDeadBound0049 :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis (49 : Fin 50))) 16 := by
  rw [show plane470LowerGenDeadBasis (49 : Fin 50) = [259, 128, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane470LowerGenSource0049 (by decide)
theorem plane470LowerGenDeadQRA (d : Fin 50) :
    QuotientRankAtLeast (spanCodes (plane470LowerGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane470LowerGenDeadBound0000
  | ⟨1, _⟩ => plane470LowerGenDeadBound0001
  | ⟨2, _⟩ => plane470LowerGenDeadBound0002
  | ⟨3, _⟩ => plane470LowerGenDeadBound0003
  | ⟨4, _⟩ => plane470LowerGenDeadBound0004
  | ⟨5, _⟩ => plane470LowerGenDeadBound0005
  | ⟨6, _⟩ => plane470LowerGenDeadBound0006
  | ⟨7, _⟩ => plane470LowerGenDeadBound0007
  | ⟨8, _⟩ => plane470LowerGenDeadBound0008
  | ⟨9, _⟩ => plane470LowerGenDeadBound0009
  | ⟨10, _⟩ => plane470LowerGenDeadBound0010
  | ⟨11, _⟩ => plane470LowerGenDeadBound0011
  | ⟨12, _⟩ => plane470LowerGenDeadBound0012
  | ⟨13, _⟩ => plane470LowerGenDeadBound0013
  | ⟨14, _⟩ => plane470LowerGenDeadBound0014
  | ⟨15, _⟩ => plane470LowerGenDeadBound0015
  | ⟨16, _⟩ => plane470LowerGenDeadBound0016
  | ⟨17, _⟩ => plane470LowerGenDeadBound0017
  | ⟨18, _⟩ => plane470LowerGenDeadBound0018
  | ⟨19, _⟩ => plane470LowerGenDeadBound0019
  | ⟨20, _⟩ => plane470LowerGenDeadBound0020
  | ⟨21, _⟩ => plane470LowerGenDeadBound0021
  | ⟨22, _⟩ => plane470LowerGenDeadBound0022
  | ⟨23, _⟩ => plane470LowerGenDeadBound0023
  | ⟨24, _⟩ => plane470LowerGenDeadBound0024
  | ⟨25, _⟩ => plane470LowerGenDeadBound0025
  | ⟨26, _⟩ => plane470LowerGenDeadBound0026
  | ⟨27, _⟩ => plane470LowerGenDeadBound0027
  | ⟨28, _⟩ => plane470LowerGenDeadBound0028
  | ⟨29, _⟩ => plane470LowerGenDeadBound0029
  | ⟨30, _⟩ => plane470LowerGenDeadBound0030
  | ⟨31, _⟩ => plane470LowerGenDeadBound0031
  | ⟨32, _⟩ => plane470LowerGenDeadBound0032
  | ⟨33, _⟩ => plane470LowerGenDeadBound0033
  | ⟨34, _⟩ => plane470LowerGenDeadBound0034
  | ⟨35, _⟩ => plane470LowerGenDeadBound0035
  | ⟨36, _⟩ => plane470LowerGenDeadBound0036
  | ⟨37, _⟩ => plane470LowerGenDeadBound0037
  | ⟨38, _⟩ => plane470LowerGenDeadBound0038
  | ⟨39, _⟩ => plane470LowerGenDeadBound0039
  | ⟨40, _⟩ => plane470LowerGenDeadBound0040
  | ⟨41, _⟩ => plane470LowerGenDeadBound0041
  | ⟨42, _⟩ => plane470LowerGenDeadBound0042
  | ⟨43, _⟩ => plane470LowerGenDeadBound0043
  | ⟨44, _⟩ => plane470LowerGenDeadBound0044
  | ⟨45, _⟩ => plane470LowerGenDeadBound0045
  | ⟨46, _⟩ => plane470LowerGenDeadBound0046
  | ⟨47, _⟩ => plane470LowerGenDeadBound0047
  | ⟨48, _⟩ => plane470LowerGenDeadBound0048
  | ⟨49, _⟩ => plane470LowerGenDeadBound0049
  | ⟨k + 50, h⟩ => by omega
end QiushiMatmul
