import QiushiGlobalOrbitUnused380Bindings00
import QiushiGlobalOrbitUnused380Bindings01
import QiushiGlobalOrbitUnused380Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane380UnusedGenSourceQRA (i : Fin 26) :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenSourceBasis i)) (plane380UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane380UnusedGenBound0000
  | ⟨1, _⟩ => plane380UnusedGenBound0001
  | ⟨2, _⟩ => plane380UnusedGenBound0002
  | ⟨3, _⟩ => plane380UnusedGenBound0003
  | ⟨4, _⟩ => plane380UnusedGenBound0004
  | ⟨5, _⟩ => plane380UnusedGenBound0005
  | ⟨6, _⟩ => plane380UnusedGenBound0006
  | ⟨7, _⟩ => plane380UnusedGenBound0007
  | ⟨8, _⟩ => plane380UnusedGenBound0008
  | ⟨9, _⟩ => plane380UnusedGenBound0009
  | ⟨10, _⟩ => plane380UnusedGenBound0010
  | ⟨11, _⟩ => plane380UnusedGenBound0011
  | ⟨12, _⟩ => plane380UnusedGenBound0012
  | ⟨13, _⟩ => plane380UnusedGenBound0013
  | ⟨14, _⟩ => plane380UnusedGenBound0014
  | ⟨15, _⟩ => plane380UnusedGenBound0015
  | ⟨16, _⟩ => plane380UnusedGenBound0016
  | ⟨17, _⟩ => plane380UnusedGenBound0017
  | ⟨18, _⟩ => plane380UnusedGenBound0018
  | ⟨19, _⟩ => plane380UnusedGenBound0019
  | ⟨20, _⟩ => plane380UnusedGenBound0020
  | ⟨21, _⟩ => plane380UnusedGenBound0021
  | ⟨22, _⟩ => plane380UnusedGenBound0022
  | ⟨23, _⟩ => plane380UnusedGenBound0023
  | ⟨24, _⟩ => plane380UnusedGenBound0024
  | ⟨25, _⟩ => plane380UnusedGenBound0025
  | ⟨k + 26, h⟩ => by omega
theorem plane380UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (0 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (0 : Fin 21) = [258, 68, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0000 (by decide)
theorem plane380UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (1 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (1 : Fin 21) = [258, 64, 19, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0001 (by decide)
theorem plane380UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (2 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (2 : Fin 21) = [258, 65, 19, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0002 (by decide)
theorem plane380UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (3 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (3 : Fin 21) = [258, 68, 32, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0004 (by decide)
theorem plane380UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (4 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (4 : Fin 21) = [258, 68, 34, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0005 (by decide)
theorem plane380UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (5 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (5 : Fin 21) = [258, 68, 35, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0006 (by decide)
theorem plane380UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (6 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (6 : Fin 21) = [258, 68, 36, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0007 (by decide)
theorem plane380UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (7 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (7 : Fin 21) = [258, 68, 37, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0008 (by decide)
theorem plane380UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (8 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (8 : Fin 21) = [258, 68, 39, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0009 (by decide)
theorem plane380UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (9 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (9 : Fin 21) = [258, 128, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0010 (by decide)
theorem plane380UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (10 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (10 : Fin 21) = [258, 130, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0011 (by decide)
theorem plane380UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (11 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (11 : Fin 21) = [258, 131, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0012 (by decide)
theorem plane380UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (12 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (12 : Fin 21) = [258, 132, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0013 (by decide)
theorem plane380UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (13 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (13 : Fin 21) = [258, 133, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0014 (by decide)
theorem plane380UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (14 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (14 : Fin 21) = [258, 135, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0015 (by decide)
theorem plane380UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (15 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (15 : Fin 21) = [258, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0016 (by decide)
theorem plane380UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (16 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (16 : Fin 21) = [258, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0017 (by decide)
theorem plane380UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (17 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (17 : Fin 21) = [258, 163, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0018 (by decide)
theorem plane380UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (18 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (18 : Fin 21) = [258, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0019 (by decide)
theorem plane380UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (19 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (19 : Fin 21) = [258, 165, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0020 (by decide)
theorem plane380UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis (20 : Fin 21))) 16 := by
  rw [show plane380UnusedGenDeadBasis (20 : Fin 21) = [258, 166, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane380UnusedGenSource0021 (by decide)
theorem plane380UnusedGenDeadQRA (d : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane380UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane380UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane380UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane380UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane380UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane380UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane380UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane380UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane380UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane380UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane380UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane380UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane380UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane380UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane380UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane380UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane380UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane380UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane380UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane380UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane380UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane380UnusedGenDeadBound0020
  | ⟨k + 21, h⟩ => by omega
end QiushiMatmul
