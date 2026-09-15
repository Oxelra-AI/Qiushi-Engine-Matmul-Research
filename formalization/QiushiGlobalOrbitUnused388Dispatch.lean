import QiushiGlobalOrbitUnused388Bindings00
import QiushiGlobalOrbitUnused388Bindings01
import QiushiGlobalOrbitUnused388Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane388UnusedGenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenSourceBasis i)) (plane388UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane388UnusedGenBound0000
  | ⟨1, _⟩ => plane388UnusedGenBound0001
  | ⟨2, _⟩ => plane388UnusedGenBound0002
  | ⟨3, _⟩ => plane388UnusedGenBound0003
  | ⟨4, _⟩ => plane388UnusedGenBound0004
  | ⟨5, _⟩ => plane388UnusedGenBound0005
  | ⟨6, _⟩ => plane388UnusedGenBound0006
  | ⟨7, _⟩ => plane388UnusedGenBound0007
  | ⟨8, _⟩ => plane388UnusedGenBound0008
  | ⟨9, _⟩ => plane388UnusedGenBound0009
  | ⟨10, _⟩ => plane388UnusedGenBound0010
  | ⟨11, _⟩ => plane388UnusedGenBound0011
  | ⟨12, _⟩ => plane388UnusedGenBound0012
  | ⟨13, _⟩ => plane388UnusedGenBound0013
  | ⟨14, _⟩ => plane388UnusedGenBound0014
  | ⟨15, _⟩ => plane388UnusedGenBound0015
  | ⟨16, _⟩ => plane388UnusedGenBound0016
  | ⟨17, _⟩ => plane388UnusedGenBound0017
  | ⟨18, _⟩ => plane388UnusedGenBound0018
  | ⟨19, _⟩ => plane388UnusedGenBound0019
  | ⟨20, _⟩ => plane388UnusedGenBound0020
  | ⟨21, _⟩ => plane388UnusedGenBound0021
  | ⟨22, _⟩ => plane388UnusedGenBound0022
  | ⟨23, _⟩ => plane388UnusedGenBound0023
  | ⟨24, _⟩ => plane388UnusedGenBound0024
  | ⟨25, _⟩ => plane388UnusedGenBound0025
  | ⟨26, _⟩ => plane388UnusedGenBound0026
  | ⟨27, _⟩ => plane388UnusedGenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane388UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (0 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (0 : Fin 21) = [164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0000 (by decide)
theorem plane388UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (1 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (1 : Fin 21) = [133, 68, 33, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0003 (by decide)
theorem plane388UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (2 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (2 : Fin 21) = [135, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0005 (by decide)
theorem plane388UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (3 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (3 : Fin 21) = [129, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0006 (by decide)
theorem plane388UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (4 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (4 : Fin 21) = [131, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0007 (by decide)
theorem plane388UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (5 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (5 : Fin 21) = [256, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0008 (by decide)
theorem plane388UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (6 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (6 : Fin 21) = [258, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0009 (by decide)
theorem plane388UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (7 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (7 : Fin 21) = [259, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0010 (by decide)
theorem plane388UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (8 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (8 : Fin 21) = [261, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0011 (by decide)
theorem plane388UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (9 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (9 : Fin 21) = [263, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0012 (by decide)
theorem plane388UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (10 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (10 : Fin 21) = [288, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0013 (by decide)
theorem plane388UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (11 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (11 : Fin 21) = [289, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0014 (by decide)
theorem plane388UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (12 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (12 : Fin 21) = [290, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0015 (by decide)
theorem plane388UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (13 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (13 : Fin 21) = [291, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0016 (by decide)
theorem plane388UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (14 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (14 : Fin 21) = [292, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0017 (by decide)
theorem plane388UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (15 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (15 : Fin 21) = [293, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0018 (by decide)
theorem plane388UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (16 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (16 : Fin 21) = [294, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0019 (by decide)
theorem plane388UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (17 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (17 : Fin 21) = [295, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0020 (by decide)
theorem plane388UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (18 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (18 : Fin 21) = [258, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0021 (by decide)
theorem plane388UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (19 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (19 : Fin 21) = [258, 135, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0025 (by decide)
theorem plane388UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis (20 : Fin 21))) 16 := by
  rw [show plane388UnusedGenDeadBasis (20 : Fin 21) = [258, 131, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane388UnusedGenSource0026 (by decide)
theorem plane388UnusedGenDeadQRA (d : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane388UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane388UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane388UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane388UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane388UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane388UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane388UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane388UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane388UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane388UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane388UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane388UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane388UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane388UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane388UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane388UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane388UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane388UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane388UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane388UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane388UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane388UnusedGenDeadBound0020
  | ⟨k + 21, h⟩ => by omega
end QiushiMatmul
