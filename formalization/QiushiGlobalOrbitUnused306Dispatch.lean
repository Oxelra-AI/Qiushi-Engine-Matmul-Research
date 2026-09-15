import QiushiGlobalOrbitUnused306Bindings00
import QiushiGlobalOrbitUnused306Bindings01
import QiushiGlobalOrbitUnused306Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane306UnusedGenSourceQRA (i : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenSourceBasis i)) (plane306UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane306UnusedGenBound0000
  | ⟨1, _⟩ => plane306UnusedGenBound0001
  | ⟨2, _⟩ => plane306UnusedGenBound0002
  | ⟨3, _⟩ => plane306UnusedGenBound0003
  | ⟨4, _⟩ => plane306UnusedGenBound0004
  | ⟨5, _⟩ => plane306UnusedGenBound0005
  | ⟨6, _⟩ => plane306UnusedGenBound0006
  | ⟨7, _⟩ => plane306UnusedGenBound0007
  | ⟨8, _⟩ => plane306UnusedGenBound0008
  | ⟨9, _⟩ => plane306UnusedGenBound0009
  | ⟨10, _⟩ => plane306UnusedGenBound0010
  | ⟨11, _⟩ => plane306UnusedGenBound0011
  | ⟨12, _⟩ => plane306UnusedGenBound0012
  | ⟨13, _⟩ => plane306UnusedGenBound0013
  | ⟨14, _⟩ => plane306UnusedGenBound0014
  | ⟨15, _⟩ => plane306UnusedGenBound0015
  | ⟨16, _⟩ => plane306UnusedGenBound0016
  | ⟨17, _⟩ => plane306UnusedGenBound0017
  | ⟨18, _⟩ => plane306UnusedGenBound0018
  | ⟨19, _⟩ => plane306UnusedGenBound0019
  | ⟨20, _⟩ => plane306UnusedGenBound0020
  | ⟨21, _⟩ => plane306UnusedGenBound0021
  | ⟨22, _⟩ => plane306UnusedGenBound0022
  | ⟨23, _⟩ => plane306UnusedGenBound0023
  | ⟨24, _⟩ => plane306UnusedGenBound0024
  | ⟨25, _⟩ => plane306UnusedGenBound0025
  | ⟨26, _⟩ => plane306UnusedGenBound0026
  | ⟨27, _⟩ => plane306UnusedGenBound0027
  | ⟨28, _⟩ => plane306UnusedGenBound0028
  | ⟨29, _⟩ => plane306UnusedGenBound0029
  | ⟨k + 30, h⟩ => by omega
theorem plane306UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (0 : Fin 14) = [132, 96, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0001 (by decide)
theorem plane306UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (1 : Fin 14) = [132, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0002 (by decide)
theorem plane306UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (2 : Fin 14) = [132, 80, 48, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0004 (by decide)
theorem plane306UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (3 : Fin 14) = [256, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0007 (by decide)
theorem plane306UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (4 : Fin 14) = [262, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0008 (by decide)
theorem plane306UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (5 : Fin 14) = [274, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0009 (by decide)
theorem plane306UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (6 : Fin 14) = [276, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0010 (by decide)
theorem plane306UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (7 : Fin 14) = [278, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0011 (by decide)
theorem plane306UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (8 : Fin 14) = [290, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0012 (by decide)
theorem plane306UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (9 : Fin 14) = [294, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0013 (by decide)
theorem plane306UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (10 : Fin 14) = [304, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0014 (by decide)
theorem plane306UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (11 : Fin 14) = [306, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0015 (by decide)
theorem plane306UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (12 : Fin 14) = [308, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0016 (by decide)
theorem plane306UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane306UnusedGenDeadBasis (13 : Fin 14) = [310, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane306UnusedGenSource0017 (by decide)
theorem plane306UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane306UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane306UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane306UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane306UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane306UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane306UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane306UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane306UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane306UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane306UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane306UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane306UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane306UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane306UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane306UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
