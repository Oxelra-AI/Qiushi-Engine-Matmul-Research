import QiushiGlobalOrbitUnused382Bindings00
import QiushiGlobalOrbitUnused382Bindings01
import QiushiGlobalOrbitUnused382Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane382UnusedGenSourceQRA (i : Fin 23) :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenSourceBasis i)) (plane382UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane382UnusedGenBound0000
  | ⟨1, _⟩ => plane382UnusedGenBound0001
  | ⟨2, _⟩ => plane382UnusedGenBound0002
  | ⟨3, _⟩ => plane382UnusedGenBound0003
  | ⟨4, _⟩ => plane382UnusedGenBound0004
  | ⟨5, _⟩ => plane382UnusedGenBound0005
  | ⟨6, _⟩ => plane382UnusedGenBound0006
  | ⟨7, _⟩ => plane382UnusedGenBound0007
  | ⟨8, _⟩ => plane382UnusedGenBound0008
  | ⟨9, _⟩ => plane382UnusedGenBound0009
  | ⟨10, _⟩ => plane382UnusedGenBound0010
  | ⟨11, _⟩ => plane382UnusedGenBound0011
  | ⟨12, _⟩ => plane382UnusedGenBound0012
  | ⟨13, _⟩ => plane382UnusedGenBound0013
  | ⟨14, _⟩ => plane382UnusedGenBound0014
  | ⟨15, _⟩ => plane382UnusedGenBound0015
  | ⟨16, _⟩ => plane382UnusedGenBound0016
  | ⟨17, _⟩ => plane382UnusedGenBound0017
  | ⟨18, _⟩ => plane382UnusedGenBound0018
  | ⟨19, _⟩ => plane382UnusedGenBound0019
  | ⟨20, _⟩ => plane382UnusedGenBound0020
  | ⟨21, _⟩ => plane382UnusedGenBound0021
  | ⟨22, _⟩ => plane382UnusedGenBound0022
  | ⟨k + 23, h⟩ => by omega
theorem plane382UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (0 : Fin 19) = [262, 68, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0000 (by decide)
theorem plane382UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (1 : Fin 19) = [258, 64, 19, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0002 (by decide)
theorem plane382UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (2 : Fin 19) = [259, 65, 19, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0003 (by decide)
theorem plane382UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (3 : Fin 19) = [262, 68, 33, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0004 (by decide)
theorem plane382UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (4 : Fin 19) = [262, 68, 35, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0005 (by decide)
theorem plane382UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (5 : Fin 19) = [262, 68, 36, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0006 (by decide)
theorem plane382UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (6 : Fin 19) = [262, 68, 39, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0007 (by decide)
theorem plane382UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (7 : Fin 19) = [262, 129, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0008 (by decide)
theorem plane382UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (8 : Fin 19) = [262, 131, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0009 (by decide)
theorem plane382UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (9 : Fin 19) = [262, 132, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0010 (by decide)
theorem plane382UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (10 : Fin 19) = [262, 135, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0011 (by decide)
theorem plane382UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (11 : Fin 19) = [262, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0012 (by decide)
theorem plane382UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (12 : Fin 19) = [262, 161, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0013 (by decide)
theorem plane382UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (13 : Fin 19) = [262, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0014 (by decide)
theorem plane382UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (14 : Fin 19) = [262, 163, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0015 (by decide)
theorem plane382UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (15 : Fin 19) = [262, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0016 (by decide)
theorem plane382UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (16 : Fin 19) = [262, 165, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0017 (by decide)
theorem plane382UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (17 : Fin 19) = [262, 166, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0018 (by decide)
theorem plane382UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane382UnusedGenDeadBasis (18 : Fin 19) = [262, 167, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane382UnusedGenSource0019 (by decide)
theorem plane382UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane382UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane382UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane382UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane382UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane382UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane382UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane382UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane382UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane382UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane382UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane382UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane382UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane382UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane382UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane382UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane382UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane382UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane382UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane382UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane382UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
