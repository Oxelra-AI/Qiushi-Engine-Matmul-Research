import QiushiGlobalOrbitUnused291Bindings00
import QiushiGlobalOrbitUnused291Bindings01
import QiushiGlobalOrbitUnused291Bindings02
import QiushiGlobalOrbitUnused291Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane291UnusedGenSourceQRA (i : Fin 33) :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenSourceBasis i)) (plane291UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane291UnusedGenBound0000
  | ⟨1, _⟩ => plane291UnusedGenBound0001
  | ⟨2, _⟩ => plane291UnusedGenBound0002
  | ⟨3, _⟩ => plane291UnusedGenBound0003
  | ⟨4, _⟩ => plane291UnusedGenBound0004
  | ⟨5, _⟩ => plane291UnusedGenBound0005
  | ⟨6, _⟩ => plane291UnusedGenBound0006
  | ⟨7, _⟩ => plane291UnusedGenBound0007
  | ⟨8, _⟩ => plane291UnusedGenBound0008
  | ⟨9, _⟩ => plane291UnusedGenBound0009
  | ⟨10, _⟩ => plane291UnusedGenBound0010
  | ⟨11, _⟩ => plane291UnusedGenBound0011
  | ⟨12, _⟩ => plane291UnusedGenBound0012
  | ⟨13, _⟩ => plane291UnusedGenBound0013
  | ⟨14, _⟩ => plane291UnusedGenBound0014
  | ⟨15, _⟩ => plane291UnusedGenBound0015
  | ⟨16, _⟩ => plane291UnusedGenBound0016
  | ⟨17, _⟩ => plane291UnusedGenBound0017
  | ⟨18, _⟩ => plane291UnusedGenBound0018
  | ⟨19, _⟩ => plane291UnusedGenBound0019
  | ⟨20, _⟩ => plane291UnusedGenBound0020
  | ⟨21, _⟩ => plane291UnusedGenBound0021
  | ⟨22, _⟩ => plane291UnusedGenBound0022
  | ⟨23, _⟩ => plane291UnusedGenBound0023
  | ⟨24, _⟩ => plane291UnusedGenBound0024
  | ⟨25, _⟩ => plane291UnusedGenBound0025
  | ⟨26, _⟩ => plane291UnusedGenBound0026
  | ⟨27, _⟩ => plane291UnusedGenBound0027
  | ⟨28, _⟩ => plane291UnusedGenBound0028
  | ⟨29, _⟩ => plane291UnusedGenBound0029
  | ⟨30, _⟩ => plane291UnusedGenBound0030
  | ⟨31, _⟩ => plane291UnusedGenBound0031
  | ⟨32, _⟩ => plane291UnusedGenBound0032
  | ⟨k + 33, h⟩ => by omega
theorem plane291UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (0 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (0 : Fin 30) = [84, 32, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0000 (by decide)
theorem plane291UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (1 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (1 : Fin 30) = [80, 32, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0001 (by decide)
theorem plane291UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (2 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (2 : Fin 30) = [68, 32, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0002 (by decide)
theorem plane291UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (3 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (3 : Fin 30) = [70, 32, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0003 (by decide)
theorem plane291UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (4 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (4 : Fin 30) = [128, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0004 (by decide)
theorem plane291UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (5 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (5 : Fin 30) = [130, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0005 (by decide)
theorem plane291UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (6 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (6 : Fin 30) = [132, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0006 (by decide)
theorem plane291UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (7 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (7 : Fin 30) = [134, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0007 (by decide)
theorem plane291UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (8 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (8 : Fin 30) = [144, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0008 (by decide)
theorem plane291UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (9 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (9 : Fin 30) = [146, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0009 (by decide)
theorem plane291UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (10 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (10 : Fin 30) = [148, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0010 (by decide)
theorem plane291UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (11 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (11 : Fin 30) = [150, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0011 (by decide)
theorem plane291UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (12 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (12 : Fin 30) = [256, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0012 (by decide)
theorem plane291UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (13 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (13 : Fin 30) = [258, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0013 (by decide)
theorem plane291UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (14 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (14 : Fin 30) = [260, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0014 (by decide)
theorem plane291UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (15 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (15 : Fin 30) = [262, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0015 (by decide)
theorem plane291UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (16 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (16 : Fin 30) = [272, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0016 (by decide)
theorem plane291UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (17 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (17 : Fin 30) = [274, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0017 (by decide)
theorem plane291UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (18 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (18 : Fin 30) = [276, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0018 (by decide)
theorem plane291UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (19 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (19 : Fin 30) = [278, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0019 (by decide)
theorem plane291UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (20 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (20 : Fin 30) = [384, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0020 (by decide)
theorem plane291UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (21 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (21 : Fin 30) = [386, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0021 (by decide)
theorem plane291UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (22 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (22 : Fin 30) = [388, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0022 (by decide)
theorem plane291UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (23 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (23 : Fin 30) = [390, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0023 (by decide)
theorem plane291UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (24 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (24 : Fin 30) = [400, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0024 (by decide)
theorem plane291UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (25 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (25 : Fin 30) = [402, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0025 (by decide)
theorem plane291UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (26 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (26 : Fin 30) = [404, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0026 (by decide)
theorem plane291UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (27 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (27 : Fin 30) = [406, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0027 (by decide)
theorem plane291UnusedGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (28 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (28 : Fin 30) = [272, 80, 32, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0029 (by decide)
theorem plane291UnusedGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis (29 : Fin 30))) 15 := by
  rw [show plane291UnusedGenDeadBasis (29 : Fin 30) = [274, 80, 32, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane291UnusedGenSource0030 (by decide)
theorem plane291UnusedGenDeadQRA (d : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane291UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane291UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane291UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane291UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane291UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane291UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane291UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane291UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane291UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane291UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane291UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane291UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane291UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane291UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane291UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane291UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane291UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane291UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane291UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane291UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane291UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane291UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane291UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane291UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane291UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane291UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane291UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane291UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane291UnusedGenDeadBound0027
  | ⟨28, _⟩ => plane291UnusedGenDeadBound0028
  | ⟨29, _⟩ => plane291UnusedGenDeadBound0029
  | ⟨k + 30, h⟩ => by omega
end QiushiMatmul
