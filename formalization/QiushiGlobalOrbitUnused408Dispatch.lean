import QiushiGlobalOrbitUnused408Bindings00
import QiushiGlobalOrbitUnused408Bindings01
import QiushiGlobalOrbitUnused408Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane408UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenSourceBasis i)) (plane408UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane408UnusedGenBound0000
  | ⟨1, _⟩ => plane408UnusedGenBound0001
  | ⟨2, _⟩ => plane408UnusedGenBound0002
  | ⟨3, _⟩ => plane408UnusedGenBound0003
  | ⟨4, _⟩ => plane408UnusedGenBound0004
  | ⟨5, _⟩ => plane408UnusedGenBound0005
  | ⟨6, _⟩ => plane408UnusedGenBound0006
  | ⟨7, _⟩ => plane408UnusedGenBound0007
  | ⟨8, _⟩ => plane408UnusedGenBound0008
  | ⟨9, _⟩ => plane408UnusedGenBound0009
  | ⟨10, _⟩ => plane408UnusedGenBound0010
  | ⟨11, _⟩ => plane408UnusedGenBound0011
  | ⟨12, _⟩ => plane408UnusedGenBound0012
  | ⟨13, _⟩ => plane408UnusedGenBound0013
  | ⟨14, _⟩ => plane408UnusedGenBound0014
  | ⟨15, _⟩ => plane408UnusedGenBound0015
  | ⟨16, _⟩ => plane408UnusedGenBound0016
  | ⟨17, _⟩ => plane408UnusedGenBound0017
  | ⟨18, _⟩ => plane408UnusedGenBound0018
  | ⟨19, _⟩ => plane408UnusedGenBound0019
  | ⟨20, _⟩ => plane408UnusedGenBound0020
  | ⟨21, _⟩ => plane408UnusedGenBound0021
  | ⟨22, _⟩ => plane408UnusedGenBound0022
  | ⟨23, _⟩ => plane408UnusedGenBound0023
  | ⟨24, _⟩ => plane408UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane408UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (0 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (0 : Fin 13) = [259, 163, 81, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0000 (by decide)
theorem plane408UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (1 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (1 : Fin 13) = [257, 163, 83, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0001 (by decide)
theorem plane408UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (2 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (2 : Fin 13) = [262, 163, 71, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0002 (by decide)
theorem plane408UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (3 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (3 : Fin 13) = [262, 163, 64, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0003 (by decide)
theorem plane408UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (4 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (4 : Fin 13) = [262, 163, 66, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0004 (by decide)
theorem plane408UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (5 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (5 : Fin 13) = [262, 131, 84, 32, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0005 (by decide)
theorem plane408UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (6 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (6 : Fin 13) = [262, 130, 84, 33, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0006 (by decide)
theorem plane408UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (7 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (7 : Fin 13) = [262, 135, 84, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0007 (by decide)
theorem plane408UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (8 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (8 : Fin 13) = [262, 132, 84, 39, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0008 (by decide)
theorem plane408UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (9 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (9 : Fin 13) = [262, 145, 84, 50, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0009 (by decide)
theorem plane408UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (10 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (10 : Fin 13) = [262, 144, 84, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0010 (by decide)
theorem plane408UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (11 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (11 : Fin 13) = [262, 151, 84, 52, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0011 (by decide)
theorem plane408UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis (12 : Fin 13))) 16 := by
  rw [show plane408UnusedGenDeadBasis (12 : Fin 13) = [262, 148, 84, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane408UnusedGenSource0012 (by decide)
theorem plane408UnusedGenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane408UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane408UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane408UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane408UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane408UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane408UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane408UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane408UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane408UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane408UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane408UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane408UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane408UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane408UnusedGenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
