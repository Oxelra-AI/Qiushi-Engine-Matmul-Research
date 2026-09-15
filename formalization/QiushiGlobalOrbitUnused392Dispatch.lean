import QiushiGlobalOrbitUnused392Bindings00
import QiushiGlobalOrbitUnused392Bindings01
import QiushiGlobalOrbitUnused392Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane392UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenSourceBasis i)) (plane392UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane392UnusedGenBound0000
  | ⟨1, _⟩ => plane392UnusedGenBound0001
  | ⟨2, _⟩ => plane392UnusedGenBound0002
  | ⟨3, _⟩ => plane392UnusedGenBound0003
  | ⟨4, _⟩ => plane392UnusedGenBound0004
  | ⟨5, _⟩ => plane392UnusedGenBound0005
  | ⟨6, _⟩ => plane392UnusedGenBound0006
  | ⟨7, _⟩ => plane392UnusedGenBound0007
  | ⟨8, _⟩ => plane392UnusedGenBound0008
  | ⟨9, _⟩ => plane392UnusedGenBound0009
  | ⟨10, _⟩ => plane392UnusedGenBound0010
  | ⟨11, _⟩ => plane392UnusedGenBound0011
  | ⟨12, _⟩ => plane392UnusedGenBound0012
  | ⟨13, _⟩ => plane392UnusedGenBound0013
  | ⟨14, _⟩ => plane392UnusedGenBound0014
  | ⟨15, _⟩ => plane392UnusedGenBound0015
  | ⟨16, _⟩ => plane392UnusedGenBound0016
  | ⟨17, _⟩ => plane392UnusedGenBound0017
  | ⟨18, _⟩ => plane392UnusedGenBound0018
  | ⟨19, _⟩ => plane392UnusedGenBound0019
  | ⟨20, _⟩ => plane392UnusedGenBound0020
  | ⟨21, _⟩ => plane392UnusedGenBound0021
  | ⟨22, _⟩ => plane392UnusedGenBound0022
  | ⟨23, _⟩ => plane392UnusedGenBound0023
  | ⟨24, _⟩ => plane392UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane392UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (0 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (0 : Fin 24) = [258, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0000 (by decide)
theorem plane392UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (1 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (1 : Fin 24) = [259, 68, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0001 (by decide)
theorem plane392UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (2 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (2 : Fin 24) = [259, 68, 33, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0002 (by decide)
theorem plane392UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (3 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (3 : Fin 24) = [259, 68, 34, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0003 (by decide)
theorem plane392UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (4 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (4 : Fin 24) = [259, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0004 (by decide)
theorem plane392UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (5 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (5 : Fin 24) = [259, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0005 (by decide)
theorem plane392UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (6 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (6 : Fin 24) = [259, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0006 (by decide)
theorem plane392UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (7 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (7 : Fin 24) = [259, 68, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0007 (by decide)
theorem plane392UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (8 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (8 : Fin 24) = [259, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0008 (by decide)
theorem plane392UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (9 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (9 : Fin 24) = [259, 128, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0009 (by decide)
theorem plane392UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (10 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (10 : Fin 24) = [259, 129, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0010 (by decide)
theorem plane392UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (11 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (11 : Fin 24) = [259, 130, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0011 (by decide)
theorem plane392UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (12 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (12 : Fin 24) = [259, 131, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0012 (by decide)
theorem plane392UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (13 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (13 : Fin 24) = [259, 132, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0013 (by decide)
theorem plane392UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (14 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (14 : Fin 24) = [259, 133, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0014 (by decide)
theorem plane392UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (15 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (15 : Fin 24) = [259, 134, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0015 (by decide)
theorem plane392UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (16 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (16 : Fin 24) = [259, 135, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0016 (by decide)
theorem plane392UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (17 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (17 : Fin 24) = [259, 160, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0017 (by decide)
theorem plane392UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (18 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (18 : Fin 24) = [259, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0018 (by decide)
theorem plane392UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (19 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (19 : Fin 24) = [259, 163, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0019 (by decide)
theorem plane392UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (20 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (20 : Fin 24) = [259, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0020 (by decide)
theorem plane392UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (21 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (21 : Fin 24) = [259, 165, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0021 (by decide)
theorem plane392UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (22 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (22 : Fin 24) = [258, 162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0022 (by decide)
theorem plane392UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis (23 : Fin 24))) 16 := by
  rw [show plane392UnusedGenDeadBasis (23 : Fin 24) = [258, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane392UnusedGenSource0023 (by decide)
theorem plane392UnusedGenDeadQRA (d : Fin 24) :
    QuotientRankAtLeast (spanCodes (plane392UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane392UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane392UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane392UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane392UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane392UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane392UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane392UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane392UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane392UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane392UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane392UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane392UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane392UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane392UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane392UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane392UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane392UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane392UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane392UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane392UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane392UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane392UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane392UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane392UnusedGenDeadBound0023
  | ⟨k + 24, h⟩ => by omega
end QiushiMatmul
