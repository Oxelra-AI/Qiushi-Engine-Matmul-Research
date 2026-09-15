import QiushiGlobalOrbitUnused395Bindings00
import QiushiGlobalOrbitUnused395Bindings01
import QiushiGlobalOrbitUnused395Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane395UnusedGenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenSourceBasis i)) (plane395UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane395UnusedGenBound0000
  | ⟨1, _⟩ => plane395UnusedGenBound0001
  | ⟨2, _⟩ => plane395UnusedGenBound0002
  | ⟨3, _⟩ => plane395UnusedGenBound0003
  | ⟨4, _⟩ => plane395UnusedGenBound0004
  | ⟨5, _⟩ => plane395UnusedGenBound0005
  | ⟨6, _⟩ => plane395UnusedGenBound0006
  | ⟨7, _⟩ => plane395UnusedGenBound0007
  | ⟨8, _⟩ => plane395UnusedGenBound0008
  | ⟨9, _⟩ => plane395UnusedGenBound0009
  | ⟨10, _⟩ => plane395UnusedGenBound0010
  | ⟨11, _⟩ => plane395UnusedGenBound0011
  | ⟨12, _⟩ => plane395UnusedGenBound0012
  | ⟨13, _⟩ => plane395UnusedGenBound0013
  | ⟨14, _⟩ => plane395UnusedGenBound0014
  | ⟨15, _⟩ => plane395UnusedGenBound0015
  | ⟨16, _⟩ => plane395UnusedGenBound0016
  | ⟨17, _⟩ => plane395UnusedGenBound0017
  | ⟨18, _⟩ => plane395UnusedGenBound0018
  | ⟨19, _⟩ => plane395UnusedGenBound0019
  | ⟨20, _⟩ => plane395UnusedGenBound0020
  | ⟨21, _⟩ => plane395UnusedGenBound0021
  | ⟨22, _⟩ => plane395UnusedGenBound0022
  | ⟨23, _⟩ => plane395UnusedGenBound0023
  | ⟨24, _⟩ => plane395UnusedGenBound0024
  | ⟨25, _⟩ => plane395UnusedGenBound0025
  | ⟨26, _⟩ => plane395UnusedGenBound0026
  | ⟨27, _⟩ => plane395UnusedGenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane395UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (0 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (0 : Fin 21) = [130, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0000 (by decide)
theorem plane395UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (1 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (1 : Fin 21) = [129, 96, 20, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0001 (by decide)
theorem plane395UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (2 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (2 : Fin 21) = [131, 67, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0003 (by decide)
theorem plane395UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (3 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (3 : Fin 21) = [131, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0004 (by decide)
theorem plane395UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (4 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (4 : Fin 21) = [131, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0005 (by decide)
theorem plane395UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (5 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (5 : Fin 21) = [131, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0006 (by decide)
theorem plane395UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (6 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (6 : Fin 21) = [256, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0007 (by decide)
theorem plane395UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (7 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (7 : Fin 21) = [257, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0008 (by decide)
theorem plane395UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (8 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (8 : Fin 21) = [259, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0009 (by decide)
theorem plane395UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (9 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (9 : Fin 21) = [260, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0010 (by decide)
theorem plane395UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (10 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (10 : Fin 21) = [261, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0011 (by decide)
theorem plane395UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (11 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (11 : Fin 21) = [262, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0012 (by decide)
theorem plane395UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (12 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (12 : Fin 21) = [263, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0013 (by decide)
theorem plane395UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (13 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (13 : Fin 21) = [289, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0014 (by decide)
theorem plane395UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (14 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (14 : Fin 21) = [290, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0015 (by decide)
theorem plane395UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (15 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (15 : Fin 21) = [291, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0016 (by decide)
theorem plane395UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (16 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (16 : Fin 21) = [292, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0017 (by decide)
theorem plane395UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (17 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (17 : Fin 21) = [293, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0018 (by decide)
theorem plane395UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (18 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (18 : Fin 21) = [294, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0019 (by decide)
theorem plane395UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (19 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (19 : Fin 21) = [295, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0020 (by decide)
theorem plane395UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis (20 : Fin 21))) 16 := by
  rw [show plane395UnusedGenDeadBasis (20 : Fin 21) = [257, 131, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane395UnusedGenSource0024 (by decide)
theorem plane395UnusedGenDeadQRA (d : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane395UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane395UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane395UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane395UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane395UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane395UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane395UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane395UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane395UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane395UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane395UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane395UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane395UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane395UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane395UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane395UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane395UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane395UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane395UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane395UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane395UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane395UnusedGenDeadBound0020
  | ⟨k + 21, h⟩ => by omega
end QiushiMatmul
