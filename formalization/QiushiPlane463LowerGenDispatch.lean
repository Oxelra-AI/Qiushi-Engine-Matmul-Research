import QiushiPlane463LowerGenBindings00
import QiushiPlane463LowerGenBindings01
import QiushiPlane463LowerGenBindings02
import QiushiPlane463LowerGenBindings03
import QiushiPlane463LowerGenBindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane463LowerGenSourceQRA (i : Fin 49) :
    QuotientRankAtLeast (spanCodes (plane463LowerGenSourceBasis i)) (plane463LowerGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane463LowerGenBound0000
  | ⟨1, _⟩ => plane463LowerGenBound0001
  | ⟨2, _⟩ => plane463LowerGenBound0002
  | ⟨3, _⟩ => plane463LowerGenBound0003
  | ⟨4, _⟩ => plane463LowerGenBound0004
  | ⟨5, _⟩ => plane463LowerGenBound0005
  | ⟨6, _⟩ => plane463LowerGenBound0006
  | ⟨7, _⟩ => plane463LowerGenBound0007
  | ⟨8, _⟩ => plane463LowerGenBound0008
  | ⟨9, _⟩ => plane463LowerGenBound0009
  | ⟨10, _⟩ => plane463LowerGenBound0010
  | ⟨11, _⟩ => plane463LowerGenBound0011
  | ⟨12, _⟩ => plane463LowerGenBound0012
  | ⟨13, _⟩ => plane463LowerGenBound0013
  | ⟨14, _⟩ => plane463LowerGenBound0014
  | ⟨15, _⟩ => plane463LowerGenBound0015
  | ⟨16, _⟩ => plane463LowerGenBound0016
  | ⟨17, _⟩ => plane463LowerGenBound0017
  | ⟨18, _⟩ => plane463LowerGenBound0018
  | ⟨19, _⟩ => plane463LowerGenBound0019
  | ⟨20, _⟩ => plane463LowerGenBound0020
  | ⟨21, _⟩ => plane463LowerGenBound0021
  | ⟨22, _⟩ => plane463LowerGenBound0022
  | ⟨23, _⟩ => plane463LowerGenBound0023
  | ⟨24, _⟩ => plane463LowerGenBound0024
  | ⟨25, _⟩ => plane463LowerGenBound0025
  | ⟨26, _⟩ => plane463LowerGenBound0026
  | ⟨27, _⟩ => plane463LowerGenBound0027
  | ⟨28, _⟩ => plane463LowerGenBound0028
  | ⟨29, _⟩ => plane463LowerGenBound0029
  | ⟨30, _⟩ => plane463LowerGenBound0030
  | ⟨31, _⟩ => plane463LowerGenBound0031
  | ⟨32, _⟩ => plane463LowerGenBound0032
  | ⟨33, _⟩ => plane463LowerGenBound0033
  | ⟨34, _⟩ => plane463LowerGenBound0034
  | ⟨35, _⟩ => plane463LowerGenBound0035
  | ⟨36, _⟩ => plane463LowerGenBound0036
  | ⟨37, _⟩ => plane463LowerGenBound0037
  | ⟨38, _⟩ => plane463LowerGenBound0038
  | ⟨39, _⟩ => plane463LowerGenBound0039
  | ⟨40, _⟩ => plane463LowerGenBound0040
  | ⟨41, _⟩ => plane463LowerGenBound0041
  | ⟨42, _⟩ => plane463LowerGenBound0042
  | ⟨43, _⟩ => plane463LowerGenBound0043
  | ⟨44, _⟩ => plane463LowerGenBound0044
  | ⟨45, _⟩ => plane463LowerGenBound0045
  | ⟨46, _⟩ => plane463LowerGenBound0046
  | ⟨47, _⟩ => plane463LowerGenBound0047
  | ⟨48, _⟩ => plane463LowerGenBound0048
  | ⟨k + 49, h⟩ => by omega
theorem plane463LowerGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (0 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (0 : Fin 45) = [162, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0000 (by decide)
theorem plane463LowerGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (1 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (1 : Fin 45) = [161, 68, 18, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0001 (by decide)
theorem plane463LowerGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (2 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (2 : Fin 45) = [166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0002 (by decide)
theorem plane463LowerGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (3 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (3 : Fin 45) = [164, 68, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0003 (by decide)
theorem plane463LowerGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (4 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (4 : Fin 45) = [131, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0004 (by decide)
theorem plane463LowerGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (5 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (5 : Fin 45) = [131, 68, 39, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0005 (by decide)
theorem plane463LowerGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (6 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (6 : Fin 45) = [130, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0006 (by decide)
theorem plane463LowerGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (7 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (7 : Fin 45) = [130, 68, 38, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0007 (by decide)
theorem plane463LowerGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (8 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (8 : Fin 45) = [129, 68, 36, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0008 (by decide)
theorem plane463LowerGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (9 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (9 : Fin 45) = [128, 68, 37, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0009 (by decide)
theorem plane463LowerGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (10 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (10 : Fin 45) = [135, 68, 33, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0010 (by decide)
theorem plane463LowerGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (11 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (11 : Fin 45) = [135, 68, 35, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0011 (by decide)
theorem plane463LowerGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (12 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (12 : Fin 45) = [134, 68, 32, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0012 (by decide)
theorem plane463LowerGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (13 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (13 : Fin 45) = [134, 68, 34, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0013 (by decide)
theorem plane463LowerGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (14 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (14 : Fin 45) = [133, 68, 32, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0014 (by decide)
theorem plane463LowerGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (15 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (15 : Fin 45) = [132, 68, 33, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0015 (by decide)
theorem plane463LowerGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (16 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (16 : Fin 45) = [256, 178, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0016 (by decide)
theorem plane463LowerGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (17 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (17 : Fin 45) = [258, 178, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0017 (by decide)
theorem plane463LowerGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (18 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (18 : Fin 45) = [260, 179, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0018 (by decide)
theorem plane463LowerGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (19 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (19 : Fin 45) = [261, 179, 68, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0019 (by decide)
theorem plane463LowerGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (20 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (20 : Fin 45) = [262, 178, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0020 (by decide)
theorem plane463LowerGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (21 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (21 : Fin 45) = [259, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0021 (by decide)
theorem plane463LowerGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (22 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (22 : Fin 45) = [258, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0022 (by decide)
theorem plane463LowerGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (23 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (23 : Fin 45) = [257, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0023 (by decide)
theorem plane463LowerGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (24 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (24 : Fin 45) = [256, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0024 (by decide)
theorem plane463LowerGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (25 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (25 : Fin 45) = [256, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0025 (by decide)
theorem plane463LowerGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (26 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (26 : Fin 45) = [256, 166, 68, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0026 (by decide)
theorem plane463LowerGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (27 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (27 : Fin 45) = [258, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0027 (by decide)
theorem plane463LowerGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (28 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (28 : Fin 45) = [256, 164, 68, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0028 (by decide)
theorem plane463LowerGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (29 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (29 : Fin 45) = [262, 149, 68, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0029 (by decide)
theorem plane463LowerGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (30 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (30 : Fin 45) = [262, 148, 68, 39, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0030 (by decide)
theorem plane463LowerGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (31 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (31 : Fin 45) = [262, 151, 68, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0031 (by decide)
theorem plane463LowerGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (32 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (32 : Fin 45) = [262, 150, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0032 (by decide)
theorem plane463LowerGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (33 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (33 : Fin 45) = [262, 145, 68, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0033 (by decide)
theorem plane463LowerGenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (34 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (34 : Fin 45) = [262, 144, 68, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0034 (by decide)
theorem plane463LowerGenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (35 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (35 : Fin 45) = [262, 147, 68, 32, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0035 (by decide)
theorem plane463LowerGenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (36 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (36 : Fin 45) = [262, 146, 68, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0036 (by decide)
theorem plane463LowerGenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (37 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (37 : Fin 45) = [262, 133, 68, 54, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0037 (by decide)
theorem plane463LowerGenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (38 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (38 : Fin 45) = [262, 132, 68, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0038 (by decide)
theorem plane463LowerGenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (39 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (39 : Fin 45) = [262, 135, 68, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0039 (by decide)
theorem plane463LowerGenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (40 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (40 : Fin 45) = [262, 134, 68, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0040 (by decide)
theorem plane463LowerGenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (41 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (41 : Fin 45) = [262, 129, 68, 50, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0041 (by decide)
theorem plane463LowerGenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (42 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (42 : Fin 45) = [262, 128, 68, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0042 (by decide)
theorem plane463LowerGenDeadBound0043 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (43 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (43 : Fin 45) = [262, 131, 68, 48, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0043 (by decide)
theorem plane463LowerGenDeadBound0044 :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis (44 : Fin 45))) 16 := by
  rw [show plane463LowerGenDeadBasis (44 : Fin 45) = [262, 130, 68, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane463LowerGenSource0044 (by decide)
theorem plane463LowerGenDeadQRA (d : Fin 45) :
    QuotientRankAtLeast (spanCodes (plane463LowerGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane463LowerGenDeadBound0000
  | ⟨1, _⟩ => plane463LowerGenDeadBound0001
  | ⟨2, _⟩ => plane463LowerGenDeadBound0002
  | ⟨3, _⟩ => plane463LowerGenDeadBound0003
  | ⟨4, _⟩ => plane463LowerGenDeadBound0004
  | ⟨5, _⟩ => plane463LowerGenDeadBound0005
  | ⟨6, _⟩ => plane463LowerGenDeadBound0006
  | ⟨7, _⟩ => plane463LowerGenDeadBound0007
  | ⟨8, _⟩ => plane463LowerGenDeadBound0008
  | ⟨9, _⟩ => plane463LowerGenDeadBound0009
  | ⟨10, _⟩ => plane463LowerGenDeadBound0010
  | ⟨11, _⟩ => plane463LowerGenDeadBound0011
  | ⟨12, _⟩ => plane463LowerGenDeadBound0012
  | ⟨13, _⟩ => plane463LowerGenDeadBound0013
  | ⟨14, _⟩ => plane463LowerGenDeadBound0014
  | ⟨15, _⟩ => plane463LowerGenDeadBound0015
  | ⟨16, _⟩ => plane463LowerGenDeadBound0016
  | ⟨17, _⟩ => plane463LowerGenDeadBound0017
  | ⟨18, _⟩ => plane463LowerGenDeadBound0018
  | ⟨19, _⟩ => plane463LowerGenDeadBound0019
  | ⟨20, _⟩ => plane463LowerGenDeadBound0020
  | ⟨21, _⟩ => plane463LowerGenDeadBound0021
  | ⟨22, _⟩ => plane463LowerGenDeadBound0022
  | ⟨23, _⟩ => plane463LowerGenDeadBound0023
  | ⟨24, _⟩ => plane463LowerGenDeadBound0024
  | ⟨25, _⟩ => plane463LowerGenDeadBound0025
  | ⟨26, _⟩ => plane463LowerGenDeadBound0026
  | ⟨27, _⟩ => plane463LowerGenDeadBound0027
  | ⟨28, _⟩ => plane463LowerGenDeadBound0028
  | ⟨29, _⟩ => plane463LowerGenDeadBound0029
  | ⟨30, _⟩ => plane463LowerGenDeadBound0030
  | ⟨31, _⟩ => plane463LowerGenDeadBound0031
  | ⟨32, _⟩ => plane463LowerGenDeadBound0032
  | ⟨33, _⟩ => plane463LowerGenDeadBound0033
  | ⟨34, _⟩ => plane463LowerGenDeadBound0034
  | ⟨35, _⟩ => plane463LowerGenDeadBound0035
  | ⟨36, _⟩ => plane463LowerGenDeadBound0036
  | ⟨37, _⟩ => plane463LowerGenDeadBound0037
  | ⟨38, _⟩ => plane463LowerGenDeadBound0038
  | ⟨39, _⟩ => plane463LowerGenDeadBound0039
  | ⟨40, _⟩ => plane463LowerGenDeadBound0040
  | ⟨41, _⟩ => plane463LowerGenDeadBound0041
  | ⟨42, _⟩ => plane463LowerGenDeadBound0042
  | ⟨43, _⟩ => plane463LowerGenDeadBound0043
  | ⟨44, _⟩ => plane463LowerGenDeadBound0044
  | ⟨k + 45, h⟩ => by omega
end QiushiMatmul
