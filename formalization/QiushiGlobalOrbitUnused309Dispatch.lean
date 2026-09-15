import QiushiGlobalOrbitUnused309Bindings00
import QiushiGlobalOrbitUnused309Bindings01
import QiushiGlobalOrbitUnused309Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane309UnusedGenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenSourceBasis i)) (plane309UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane309UnusedGenBound0000
  | ⟨1, _⟩ => plane309UnusedGenBound0001
  | ⟨2, _⟩ => plane309UnusedGenBound0002
  | ⟨3, _⟩ => plane309UnusedGenBound0003
  | ⟨4, _⟩ => plane309UnusedGenBound0004
  | ⟨5, _⟩ => plane309UnusedGenBound0005
  | ⟨6, _⟩ => plane309UnusedGenBound0006
  | ⟨7, _⟩ => plane309UnusedGenBound0007
  | ⟨8, _⟩ => plane309UnusedGenBound0008
  | ⟨9, _⟩ => plane309UnusedGenBound0009
  | ⟨10, _⟩ => plane309UnusedGenBound0010
  | ⟨11, _⟩ => plane309UnusedGenBound0011
  | ⟨12, _⟩ => plane309UnusedGenBound0012
  | ⟨13, _⟩ => plane309UnusedGenBound0013
  | ⟨14, _⟩ => plane309UnusedGenBound0014
  | ⟨15, _⟩ => plane309UnusedGenBound0015
  | ⟨16, _⟩ => plane309UnusedGenBound0016
  | ⟨17, _⟩ => plane309UnusedGenBound0017
  | ⟨18, _⟩ => plane309UnusedGenBound0018
  | ⟨19, _⟩ => plane309UnusedGenBound0019
  | ⟨20, _⟩ => plane309UnusedGenBound0020
  | ⟨21, _⟩ => plane309UnusedGenBound0021
  | ⟨22, _⟩ => plane309UnusedGenBound0022
  | ⟨23, _⟩ => plane309UnusedGenBound0023
  | ⟨24, _⟩ => plane309UnusedGenBound0024
  | ⟨25, _⟩ => plane309UnusedGenBound0025
  | ⟨26, _⟩ => plane309UnusedGenBound0026
  | ⟨27, _⟩ => plane309UnusedGenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane309UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (0 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (0 : Fin 16) = [290, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0001 (by decide)
theorem plane309UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (1 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (1 : Fin 16) = [290, 96, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0002 (by decide)
theorem plane309UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (2 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (2 : Fin 16) = [262, 68, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0003 (by decide)
theorem plane309UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (3 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (3 : Fin 16) = [260, 70, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0004 (by decide)
theorem plane309UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (4 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (4 : Fin 16) = [290, 128, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0005 (by decide)
theorem plane309UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (5 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (5 : Fin 16) = [290, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0006 (by decide)
theorem plane309UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (6 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (6 : Fin 16) = [290, 134, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0007 (by decide)
theorem plane309UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (7 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (7 : Fin 16) = [290, 144, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0008 (by decide)
theorem plane309UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (8 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (8 : Fin 16) = [290, 148, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0009 (by decide)
theorem plane309UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (9 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (9 : Fin 16) = [290, 150, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0010 (by decide)
theorem plane309UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (10 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (10 : Fin 16) = [290, 160, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0011 (by decide)
theorem plane309UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (11 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (11 : Fin 16) = [290, 164, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0012 (by decide)
theorem plane309UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (12 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (12 : Fin 16) = [290, 166, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0013 (by decide)
theorem plane309UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (13 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (13 : Fin 16) = [290, 178, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0014 (by decide)
theorem plane309UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (14 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (14 : Fin 16) = [290, 180, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0015 (by decide)
theorem plane309UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis (15 : Fin 16))) 16 := by
  rw [show plane309UnusedGenDeadBasis (15 : Fin 16) = [290, 182, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane309UnusedGenSource0016 (by decide)
theorem plane309UnusedGenDeadQRA (d : Fin 16) :
    QuotientRankAtLeast (spanCodes (plane309UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane309UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane309UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane309UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane309UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane309UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane309UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane309UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane309UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane309UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane309UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane309UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane309UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane309UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane309UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane309UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane309UnusedGenDeadBound0015
  | ⟨k + 16, h⟩ => by omega
end QiushiMatmul
