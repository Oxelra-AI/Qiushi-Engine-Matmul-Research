import QiushiGlobalOrbitUnused308Bindings00
import QiushiGlobalOrbitUnused308Bindings01
import QiushiGlobalOrbitUnused308Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane308UnusedGenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenSourceBasis i)) (plane308UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane308UnusedGenBound0000
  | ⟨1, _⟩ => plane308UnusedGenBound0001
  | ⟨2, _⟩ => plane308UnusedGenBound0002
  | ⟨3, _⟩ => plane308UnusedGenBound0003
  | ⟨4, _⟩ => plane308UnusedGenBound0004
  | ⟨5, _⟩ => plane308UnusedGenBound0005
  | ⟨6, _⟩ => plane308UnusedGenBound0006
  | ⟨7, _⟩ => plane308UnusedGenBound0007
  | ⟨8, _⟩ => plane308UnusedGenBound0008
  | ⟨9, _⟩ => plane308UnusedGenBound0009
  | ⟨10, _⟩ => plane308UnusedGenBound0010
  | ⟨11, _⟩ => plane308UnusedGenBound0011
  | ⟨12, _⟩ => plane308UnusedGenBound0012
  | ⟨13, _⟩ => plane308UnusedGenBound0013
  | ⟨14, _⟩ => plane308UnusedGenBound0014
  | ⟨15, _⟩ => plane308UnusedGenBound0015
  | ⟨16, _⟩ => plane308UnusedGenBound0016
  | ⟨17, _⟩ => plane308UnusedGenBound0017
  | ⟨18, _⟩ => plane308UnusedGenBound0018
  | ⟨19, _⟩ => plane308UnusedGenBound0019
  | ⟨20, _⟩ => plane308UnusedGenBound0020
  | ⟨21, _⟩ => plane308UnusedGenBound0021
  | ⟨22, _⟩ => plane308UnusedGenBound0022
  | ⟨23, _⟩ => plane308UnusedGenBound0023
  | ⟨24, _⟩ => plane308UnusedGenBound0024
  | ⟨25, _⟩ => plane308UnusedGenBound0025
  | ⟨26, _⟩ => plane308UnusedGenBound0026
  | ⟨27, _⟩ => plane308UnusedGenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane308UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (0 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (0 : Fin 19) = [288, 96, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0000 (by decide)
theorem plane308UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (1 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (1 : Fin 19) = [288, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0001 (by decide)
theorem plane308UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (2 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (2 : Fin 19) = [288, 96, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0002 (by decide)
theorem plane308UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (3 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (3 : Fin 19) = [256, 64, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0003 (by decide)
theorem plane308UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (4 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (4 : Fin 19) = [258, 66, 34, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0004 (by decide)
theorem plane308UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (5 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (5 : Fin 19) = [260, 68, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0005 (by decide)
theorem plane308UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (6 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (6 : Fin 19) = [262, 70, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0006 (by decide)
theorem plane308UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (7 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (7 : Fin 19) = [276, 84, 52, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0007 (by decide)
theorem plane308UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (8 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (8 : Fin 19) = [278, 86, 54, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0008 (by decide)
theorem plane308UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (9 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (9 : Fin 19) = [288, 130, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0009 (by decide)
theorem plane308UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (10 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (10 : Fin 19) = [288, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0010 (by decide)
theorem plane308UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (11 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (11 : Fin 19) = [288, 146, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0011 (by decide)
theorem plane308UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (12 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (12 : Fin 19) = [288, 148, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0012 (by decide)
theorem plane308UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (13 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (13 : Fin 19) = [288, 162, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0013 (by decide)
theorem plane308UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (14 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (14 : Fin 19) = [288, 164, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0014 (by decide)
theorem plane308UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (15 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (15 : Fin 19) = [288, 176, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0015 (by decide)
theorem plane308UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (16 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (16 : Fin 19) = [288, 182, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0016 (by decide)
theorem plane308UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (17 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (17 : Fin 19) = [256, 132, 64, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0017 (by decide)
theorem plane308UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis (18 : Fin 19))) 15 := by
  rw [show plane308UnusedGenDeadBasis (18 : Fin 19) = [258, 148, 66, 34, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane308UnusedGenSource0018 (by decide)
theorem plane308UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane308UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane308UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane308UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane308UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane308UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane308UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane308UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane308UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane308UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane308UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane308UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane308UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane308UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane308UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane308UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane308UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane308UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane308UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane308UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane308UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
