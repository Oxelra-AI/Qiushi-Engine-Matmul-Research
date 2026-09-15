import QiushiGlobalOrbitUnused407Bindings00
import QiushiGlobalOrbitUnused407Bindings01
import QiushiGlobalOrbitUnused407Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane407UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenSourceBasis i)) (plane407UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane407UnusedGenBound0000
  | ⟨1, _⟩ => plane407UnusedGenBound0001
  | ⟨2, _⟩ => plane407UnusedGenBound0002
  | ⟨3, _⟩ => plane407UnusedGenBound0003
  | ⟨4, _⟩ => plane407UnusedGenBound0004
  | ⟨5, _⟩ => plane407UnusedGenBound0005
  | ⟨6, _⟩ => plane407UnusedGenBound0006
  | ⟨7, _⟩ => plane407UnusedGenBound0007
  | ⟨8, _⟩ => plane407UnusedGenBound0008
  | ⟨9, _⟩ => plane407UnusedGenBound0009
  | ⟨10, _⟩ => plane407UnusedGenBound0010
  | ⟨11, _⟩ => plane407UnusedGenBound0011
  | ⟨12, _⟩ => plane407UnusedGenBound0012
  | ⟨13, _⟩ => plane407UnusedGenBound0013
  | ⟨14, _⟩ => plane407UnusedGenBound0014
  | ⟨15, _⟩ => plane407UnusedGenBound0015
  | ⟨16, _⟩ => plane407UnusedGenBound0016
  | ⟨17, _⟩ => plane407UnusedGenBound0017
  | ⟨18, _⟩ => plane407UnusedGenBound0018
  | ⟨19, _⟩ => plane407UnusedGenBound0019
  | ⟨20, _⟩ => plane407UnusedGenBound0020
  | ⟨21, _⟩ => plane407UnusedGenBound0021
  | ⟨22, _⟩ => plane407UnusedGenBound0022
  | ⟨23, _⟩ => plane407UnusedGenBound0023
  | ⟨24, _⟩ => plane407UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane407UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (0 : Fin 19) = [257, 163, 80, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0000 (by decide)
theorem plane407UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (1 : Fin 19) = [257, 163, 81, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0001 (by decide)
theorem plane407UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (2 : Fin 19) = [257, 163, 82, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0002 (by decide)
theorem plane407UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (3 : Fin 19) = [257, 163, 83, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0003 (by decide)
theorem plane407UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (4 : Fin 19) = [257, 163, 71, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0004 (by decide)
theorem plane407UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (5 : Fin 19) = [257, 163, 64, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0005 (by decide)
theorem plane407UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (6 : Fin 19) = [257, 163, 65, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0006 (by decide)
theorem plane407UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (7 : Fin 19) = [257, 163, 66, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0007 (by decide)
theorem plane407UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (8 : Fin 19) = [257, 163, 67, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0008 (by decide)
theorem plane407UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (9 : Fin 19) = [257, 131, 84, 32, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0009 (by decide)
theorem plane407UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (10 : Fin 19) = [257, 130, 84, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0010 (by decide)
theorem plane407UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (11 : Fin 19) = [257, 129, 84, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0011 (by decide)
theorem plane407UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (12 : Fin 19) = [257, 128, 84, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0012 (by decide)
theorem plane407UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (13 : Fin 19) = [257, 133, 84, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0013 (by decide)
theorem plane407UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (14 : Fin 19) = [257, 132, 84, 39, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0014 (by decide)
theorem plane407UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (15 : Fin 19) = [257, 147, 84, 48, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0015 (by decide)
theorem plane407UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (16 : Fin 19) = [257, 144, 84, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0016 (by decide)
theorem plane407UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (17 : Fin 19) = [257, 151, 84, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0017 (by decide)
theorem plane407UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane407UnusedGenDeadBasis (18 : Fin 19) = [257, 150, 84, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane407UnusedGenSource0018 (by decide)
theorem plane407UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane407UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane407UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane407UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane407UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane407UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane407UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane407UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane407UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane407UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane407UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane407UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane407UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane407UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane407UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane407UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane407UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane407UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane407UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane407UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane407UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
