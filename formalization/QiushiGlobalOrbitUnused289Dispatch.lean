import QiushiGlobalOrbitUnused289Bindings00
import QiushiGlobalOrbitUnused289Bindings01
import QiushiGlobalOrbitUnused289Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane289UnusedGenSourceQRA (i : Fin 27) :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenSourceBasis i)) (plane289UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane289UnusedGenBound0000
  | ⟨1, _⟩ => plane289UnusedGenBound0001
  | ⟨2, _⟩ => plane289UnusedGenBound0002
  | ⟨3, _⟩ => plane289UnusedGenBound0003
  | ⟨4, _⟩ => plane289UnusedGenBound0004
  | ⟨5, _⟩ => plane289UnusedGenBound0005
  | ⟨6, _⟩ => plane289UnusedGenBound0006
  | ⟨7, _⟩ => plane289UnusedGenBound0007
  | ⟨8, _⟩ => plane289UnusedGenBound0008
  | ⟨9, _⟩ => plane289UnusedGenBound0009
  | ⟨10, _⟩ => plane289UnusedGenBound0010
  | ⟨11, _⟩ => plane289UnusedGenBound0011
  | ⟨12, _⟩ => plane289UnusedGenBound0012
  | ⟨13, _⟩ => plane289UnusedGenBound0013
  | ⟨14, _⟩ => plane289UnusedGenBound0014
  | ⟨15, _⟩ => plane289UnusedGenBound0015
  | ⟨16, _⟩ => plane289UnusedGenBound0016
  | ⟨17, _⟩ => plane289UnusedGenBound0017
  | ⟨18, _⟩ => plane289UnusedGenBound0018
  | ⟨19, _⟩ => plane289UnusedGenBound0019
  | ⟨20, _⟩ => plane289UnusedGenBound0020
  | ⟨21, _⟩ => plane289UnusedGenBound0021
  | ⟨22, _⟩ => plane289UnusedGenBound0022
  | ⟨23, _⟩ => plane289UnusedGenBound0023
  | ⟨24, _⟩ => plane289UnusedGenBound0024
  | ⟨25, _⟩ => plane289UnusedGenBound0025
  | ⟨26, _⟩ => plane289UnusedGenBound0026
  | ⟨k + 27, h⟩ => by omega
theorem plane289UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (0 : Fin 14) = [258, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0001 (by decide)
theorem plane289UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (1 : Fin 14) = [258, 36, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0002 (by decide)
theorem plane289UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (2 : Fin 14) = [258, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0003 (by decide)
theorem plane289UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (3 : Fin 14) = [258, 70, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0004 (by decide)
theorem plane289UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (4 : Fin 14) = [258, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0005 (by decide)
theorem plane289UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (5 : Fin 14) = [258, 98, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0006 (by decide)
theorem plane289UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (6 : Fin 14) = [258, 100, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0007 (by decide)
theorem plane289UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (7 : Fin 14) = [258, 102, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0008 (by decide)
theorem plane289UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (8 : Fin 14) = [258, 162, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0009 (by decide)
theorem plane289UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (9 : Fin 14) = [258, 164, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0010 (by decide)
theorem plane289UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (10 : Fin 14) = [258, 224, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0011 (by decide)
theorem plane289UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (11 : Fin 14) = [258, 230, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0012 (by decide)
theorem plane289UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (12 : Fin 14) = [258, 162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0014 (by decide)
theorem plane289UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane289UnusedGenDeadBasis (13 : Fin 14) = [258, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane289UnusedGenSource0015 (by decide)
theorem plane289UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane289UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane289UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane289UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane289UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane289UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane289UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane289UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane289UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane289UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane289UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane289UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane289UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane289UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane289UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane289UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
