import QiushiGlobalOrbitUnused273Bindings00
import QiushiGlobalOrbitUnused273Bindings01
import QiushiGlobalOrbitUnused273Bindings02
import QiushiGlobalOrbitUnused273Bindings03
import QiushiGlobalOrbitUnused273Bindings04
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane273UnusedGenSourceQRA (i : Fin 44) :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenSourceBasis i)) (plane273UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane273UnusedGenBound0000
  | ⟨1, _⟩ => plane273UnusedGenBound0001
  | ⟨2, _⟩ => plane273UnusedGenBound0002
  | ⟨3, _⟩ => plane273UnusedGenBound0003
  | ⟨4, _⟩ => plane273UnusedGenBound0004
  | ⟨5, _⟩ => plane273UnusedGenBound0005
  | ⟨6, _⟩ => plane273UnusedGenBound0006
  | ⟨7, _⟩ => plane273UnusedGenBound0007
  | ⟨8, _⟩ => plane273UnusedGenBound0008
  | ⟨9, _⟩ => plane273UnusedGenBound0009
  | ⟨10, _⟩ => plane273UnusedGenBound0010
  | ⟨11, _⟩ => plane273UnusedGenBound0011
  | ⟨12, _⟩ => plane273UnusedGenBound0012
  | ⟨13, _⟩ => plane273UnusedGenBound0013
  | ⟨14, _⟩ => plane273UnusedGenBound0014
  | ⟨15, _⟩ => plane273UnusedGenBound0015
  | ⟨16, _⟩ => plane273UnusedGenBound0016
  | ⟨17, _⟩ => plane273UnusedGenBound0017
  | ⟨18, _⟩ => plane273UnusedGenBound0018
  | ⟨19, _⟩ => plane273UnusedGenBound0019
  | ⟨20, _⟩ => plane273UnusedGenBound0020
  | ⟨21, _⟩ => plane273UnusedGenBound0021
  | ⟨22, _⟩ => plane273UnusedGenBound0022
  | ⟨23, _⟩ => plane273UnusedGenBound0023
  | ⟨24, _⟩ => plane273UnusedGenBound0024
  | ⟨25, _⟩ => plane273UnusedGenBound0025
  | ⟨26, _⟩ => plane273UnusedGenBound0026
  | ⟨27, _⟩ => plane273UnusedGenBound0027
  | ⟨28, _⟩ => plane273UnusedGenBound0028
  | ⟨29, _⟩ => plane273UnusedGenBound0029
  | ⟨30, _⟩ => plane273UnusedGenBound0030
  | ⟨31, _⟩ => plane273UnusedGenBound0031
  | ⟨32, _⟩ => plane273UnusedGenBound0032
  | ⟨33, _⟩ => plane273UnusedGenBound0033
  | ⟨34, _⟩ => plane273UnusedGenBound0034
  | ⟨35, _⟩ => plane273UnusedGenBound0035
  | ⟨36, _⟩ => plane273UnusedGenBound0036
  | ⟨37, _⟩ => plane273UnusedGenBound0037
  | ⟨38, _⟩ => plane273UnusedGenBound0038
  | ⟨39, _⟩ => plane273UnusedGenBound0039
  | ⟨40, _⟩ => plane273UnusedGenBound0040
  | ⟨41, _⟩ => plane273UnusedGenBound0041
  | ⟨42, _⟩ => plane273UnusedGenBound0042
  | ⟨43, _⟩ => plane273UnusedGenBound0043
  | ⟨k + 44, h⟩ => by omega
theorem plane273UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (0 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (0 : Fin 43) = [148, 80, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0000 (by decide)
theorem plane273UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (1 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (1 : Fin 43) = [144, 80, 12, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0001 (by decide)
theorem plane273UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (2 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (2 : Fin 43) = [140, 64, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0002 (by decide)
theorem plane273UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (3 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (3 : Fin 43) = [136, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0003 (by decide)
theorem plane273UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (4 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (4 : Fin 43) = [132, 72, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0004 (by decide)
theorem plane273UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (5 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (5 : Fin 43) = [128, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0005 (by decide)
theorem plane273UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (6 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (6 : Fin 43) = [156, 80, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0006 (by decide)
theorem plane273UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (7 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (7 : Fin 43) = [156, 80, 36, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0007 (by decide)
theorem plane273UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (8 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (8 : Fin 43) = [156, 80, 40, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0008 (by decide)
theorem plane273UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (9 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (9 : Fin 43) = [156, 80, 44, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0009 (by decide)
theorem plane273UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (10 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (10 : Fin 43) = [156, 80, 48, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0010 (by decide)
theorem plane273UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (11 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (11 : Fin 43) = [156, 80, 52, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0011 (by decide)
theorem plane273UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (12 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (12 : Fin 43) = [156, 80, 56, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0012 (by decide)
theorem plane273UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (13 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (13 : Fin 43) = [156, 80, 60, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0013 (by decide)
theorem plane273UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (14 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (14 : Fin 43) = [256, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0014 (by decide)
theorem plane273UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (15 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (15 : Fin 43) = [260, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0015 (by decide)
theorem plane273UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (16 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (16 : Fin 43) = [264, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0016 (by decide)
theorem plane273UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (17 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (17 : Fin 43) = [268, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0017 (by decide)
theorem plane273UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (18 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (18 : Fin 43) = [272, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0018 (by decide)
theorem plane273UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (19 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (19 : Fin 43) = [276, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0019 (by decide)
theorem plane273UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (20 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (20 : Fin 43) = [280, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0020 (by decide)
theorem plane273UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (21 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (21 : Fin 43) = [284, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0021 (by decide)
theorem plane273UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (22 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (22 : Fin 43) = [288, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0022 (by decide)
theorem plane273UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (23 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (23 : Fin 43) = [292, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0023 (by decide)
theorem plane273UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (24 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (24 : Fin 43) = [296, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0024 (by decide)
theorem plane273UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (25 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (25 : Fin 43) = [300, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0025 (by decide)
theorem plane273UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (26 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (26 : Fin 43) = [304, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0026 (by decide)
theorem plane273UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (27 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (27 : Fin 43) = [308, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0027 (by decide)
theorem plane273UnusedGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (28 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (28 : Fin 43) = [312, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0028 (by decide)
theorem plane273UnusedGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (29 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (29 : Fin 43) = [316, 156, 80, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0029 (by decide)
theorem plane273UnusedGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (30 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (30 : Fin 43) = [128, 68, 20, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0031 (by decide)
theorem plane273UnusedGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (31 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (31 : Fin 43) = [148, 80, 32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0032 (by decide)
theorem plane273UnusedGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (32 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (32 : Fin 43) = [148, 80, 36, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0033 (by decide)
theorem plane273UnusedGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (33 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (33 : Fin 43) = [148, 80, 48, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0034 (by decide)
theorem plane273UnusedGenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (34 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (34 : Fin 43) = [148, 80, 52, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0035 (by decide)
theorem plane273UnusedGenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (35 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (35 : Fin 43) = [288, 136, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0036 (by decide)
theorem plane273UnusedGenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (36 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (36 : Fin 43) = [292, 136, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0037 (by decide)
theorem plane273UnusedGenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (37 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (37 : Fin 43) = [296, 136, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0038 (by decide)
theorem plane273UnusedGenDeadBound0038 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (38 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (38 : Fin 43) = [300, 136, 68, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0039 (by decide)
theorem plane273UnusedGenDeadBound0039 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (39 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (39 : Fin 43) = [256, 128, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0040 (by decide)
theorem plane273UnusedGenDeadBound0040 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (40 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (40 : Fin 43) = [260, 128, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0041 (by decide)
theorem plane273UnusedGenDeadBound0041 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (41 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (41 : Fin 43) = [264, 128, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0042 (by decide)
theorem plane273UnusedGenDeadBound0042 :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis (42 : Fin 43))) 15 := by
  rw [show plane273UnusedGenDeadBasis (42 : Fin 43) = [268, 128, 76, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane273UnusedGenSource0043 (by decide)
theorem plane273UnusedGenDeadQRA (d : Fin 43) :
    QuotientRankAtLeast (spanCodes (plane273UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane273UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane273UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane273UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane273UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane273UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane273UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane273UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane273UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane273UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane273UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane273UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane273UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane273UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane273UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane273UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane273UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane273UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane273UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane273UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane273UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane273UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane273UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane273UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane273UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane273UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane273UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane273UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane273UnusedGenDeadBound0027
  | ⟨28, _⟩ => plane273UnusedGenDeadBound0028
  | ⟨29, _⟩ => plane273UnusedGenDeadBound0029
  | ⟨30, _⟩ => plane273UnusedGenDeadBound0030
  | ⟨31, _⟩ => plane273UnusedGenDeadBound0031
  | ⟨32, _⟩ => plane273UnusedGenDeadBound0032
  | ⟨33, _⟩ => plane273UnusedGenDeadBound0033
  | ⟨34, _⟩ => plane273UnusedGenDeadBound0034
  | ⟨35, _⟩ => plane273UnusedGenDeadBound0035
  | ⟨36, _⟩ => plane273UnusedGenDeadBound0036
  | ⟨37, _⟩ => plane273UnusedGenDeadBound0037
  | ⟨38, _⟩ => plane273UnusedGenDeadBound0038
  | ⟨39, _⟩ => plane273UnusedGenDeadBound0039
  | ⟨40, _⟩ => plane273UnusedGenDeadBound0040
  | ⟨41, _⟩ => plane273UnusedGenDeadBound0041
  | ⟨42, _⟩ => plane273UnusedGenDeadBound0042
  | ⟨k + 43, h⟩ => by omega
end QiushiMatmul
