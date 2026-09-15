import QiushiGlobalOrbitUnused284Bindings00
import QiushiGlobalOrbitUnused284Bindings01
import QiushiGlobalOrbitUnused284Bindings02
import QiushiGlobalOrbitUnused284Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane284UnusedGenSourceQRA (i : Fin 34) :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenSourceBasis i)) (plane284UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane284UnusedGenBound0000
  | ⟨1, _⟩ => plane284UnusedGenBound0001
  | ⟨2, _⟩ => plane284UnusedGenBound0002
  | ⟨3, _⟩ => plane284UnusedGenBound0003
  | ⟨4, _⟩ => plane284UnusedGenBound0004
  | ⟨5, _⟩ => plane284UnusedGenBound0005
  | ⟨6, _⟩ => plane284UnusedGenBound0006
  | ⟨7, _⟩ => plane284UnusedGenBound0007
  | ⟨8, _⟩ => plane284UnusedGenBound0008
  | ⟨9, _⟩ => plane284UnusedGenBound0009
  | ⟨10, _⟩ => plane284UnusedGenBound0010
  | ⟨11, _⟩ => plane284UnusedGenBound0011
  | ⟨12, _⟩ => plane284UnusedGenBound0012
  | ⟨13, _⟩ => plane284UnusedGenBound0013
  | ⟨14, _⟩ => plane284UnusedGenBound0014
  | ⟨15, _⟩ => plane284UnusedGenBound0015
  | ⟨16, _⟩ => plane284UnusedGenBound0016
  | ⟨17, _⟩ => plane284UnusedGenBound0017
  | ⟨18, _⟩ => plane284UnusedGenBound0018
  | ⟨19, _⟩ => plane284UnusedGenBound0019
  | ⟨20, _⟩ => plane284UnusedGenBound0020
  | ⟨21, _⟩ => plane284UnusedGenBound0021
  | ⟨22, _⟩ => plane284UnusedGenBound0022
  | ⟨23, _⟩ => plane284UnusedGenBound0023
  | ⟨24, _⟩ => plane284UnusedGenBound0024
  | ⟨25, _⟩ => plane284UnusedGenBound0025
  | ⟨26, _⟩ => plane284UnusedGenBound0026
  | ⟨27, _⟩ => plane284UnusedGenBound0027
  | ⟨28, _⟩ => plane284UnusedGenBound0028
  | ⟨29, _⟩ => plane284UnusedGenBound0029
  | ⟨30, _⟩ => plane284UnusedGenBound0030
  | ⟨31, _⟩ => plane284UnusedGenBound0031
  | ⟨32, _⟩ => plane284UnusedGenBound0032
  | ⟨33, _⟩ => plane284UnusedGenBound0033
  | ⟨k + 34, h⟩ => by omega
theorem plane284UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (0 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (0 : Fin 33) = [68, 20, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0000 (by decide)
theorem plane284UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (1 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (1 : Fin 33) = [68, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0001 (by decide)
theorem plane284UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (2 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (2 : Fin 33) = [68, 34, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0002 (by decide)
theorem plane284UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (3 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (3 : Fin 33) = [68, 36, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0003 (by decide)
theorem plane284UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (4 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (4 : Fin 33) = [68, 38, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0004 (by decide)
theorem plane284UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (5 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (5 : Fin 33) = [128, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0005 (by decide)
theorem plane284UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (6 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (6 : Fin 33) = [130, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0006 (by decide)
theorem plane284UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (7 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (7 : Fin 33) = [132, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0007 (by decide)
theorem plane284UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (8 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (8 : Fin 33) = [134, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0008 (by decide)
theorem plane284UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (9 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (9 : Fin 33) = [160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0009 (by decide)
theorem plane284UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (10 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (10 : Fin 33) = [162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0010 (by decide)
theorem plane284UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (11 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (11 : Fin 33) = [164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0011 (by decide)
theorem plane284UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (12 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (12 : Fin 33) = [166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0012 (by decide)
theorem plane284UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (13 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (13 : Fin 33) = [256, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0013 (by decide)
theorem plane284UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (14 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (14 : Fin 33) = [258, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0014 (by decide)
theorem plane284UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (15 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (15 : Fin 33) = [260, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0015 (by decide)
theorem plane284UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (16 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (16 : Fin 33) = [262, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0016 (by decide)
theorem plane284UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (17 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (17 : Fin 33) = [288, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0017 (by decide)
theorem plane284UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (18 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (18 : Fin 33) = [290, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0018 (by decide)
theorem plane284UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (19 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (19 : Fin 33) = [292, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0019 (by decide)
theorem plane284UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (20 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (20 : Fin 33) = [294, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0020 (by decide)
theorem plane284UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (21 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (21 : Fin 33) = [384, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0021 (by decide)
theorem plane284UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (22 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (22 : Fin 33) = [386, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0022 (by decide)
theorem plane284UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (23 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (23 : Fin 33) = [388, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0023 (by decide)
theorem plane284UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (24 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (24 : Fin 33) = [390, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0024 (by decide)
theorem plane284UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (25 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (25 : Fin 33) = [416, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0025 (by decide)
theorem plane284UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (26 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (26 : Fin 33) = [418, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0026 (by decide)
theorem plane284UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (27 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (27 : Fin 33) = [420, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0027 (by decide)
theorem plane284UnusedGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (28 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (28 : Fin 33) = [422, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0028 (by decide)
theorem plane284UnusedGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (29 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (29 : Fin 33) = [262, 160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0030 (by decide)
theorem plane284UnusedGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (30 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (30 : Fin 33) = [258, 162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0031 (by decide)
theorem plane284UnusedGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (31 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (31 : Fin 33) = [258, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0032 (by decide)
theorem plane284UnusedGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis (32 : Fin 33))) 16 := by
  rw [show plane284UnusedGenDeadBasis (32 : Fin 33) = [262, 166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane284UnusedGenSource0033 (by decide)
theorem plane284UnusedGenDeadQRA (d : Fin 33) :
    QuotientRankAtLeast (spanCodes (plane284UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane284UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane284UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane284UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane284UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane284UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane284UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane284UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane284UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane284UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane284UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane284UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane284UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane284UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane284UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane284UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane284UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane284UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane284UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane284UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane284UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane284UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane284UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane284UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane284UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane284UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane284UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane284UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane284UnusedGenDeadBound0027
  | ⟨28, _⟩ => plane284UnusedGenDeadBound0028
  | ⟨29, _⟩ => plane284UnusedGenDeadBound0029
  | ⟨30, _⟩ => plane284UnusedGenDeadBound0030
  | ⟨31, _⟩ => plane284UnusedGenDeadBound0031
  | ⟨32, _⟩ => plane284UnusedGenDeadBound0032
  | ⟨k + 33, h⟩ => by omega
end QiushiMatmul
