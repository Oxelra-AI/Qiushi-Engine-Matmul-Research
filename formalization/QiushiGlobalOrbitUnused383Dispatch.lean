import QiushiGlobalOrbitUnused383Bindings00
import QiushiGlobalOrbitUnused383Bindings01
import QiushiGlobalOrbitUnused383Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane383UnusedGenSourceQRA (i : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenSourceBasis i)) (plane383UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane383UnusedGenBound0000
  | ⟨1, _⟩ => plane383UnusedGenBound0001
  | ⟨2, _⟩ => plane383UnusedGenBound0002
  | ⟨3, _⟩ => plane383UnusedGenBound0003
  | ⟨4, _⟩ => plane383UnusedGenBound0004
  | ⟨5, _⟩ => plane383UnusedGenBound0005
  | ⟨6, _⟩ => plane383UnusedGenBound0006
  | ⟨7, _⟩ => plane383UnusedGenBound0007
  | ⟨8, _⟩ => plane383UnusedGenBound0008
  | ⟨9, _⟩ => plane383UnusedGenBound0009
  | ⟨10, _⟩ => plane383UnusedGenBound0010
  | ⟨11, _⟩ => plane383UnusedGenBound0011
  | ⟨12, _⟩ => plane383UnusedGenBound0012
  | ⟨13, _⟩ => plane383UnusedGenBound0013
  | ⟨14, _⟩ => plane383UnusedGenBound0014
  | ⟨15, _⟩ => plane383UnusedGenBound0015
  | ⟨16, _⟩ => plane383UnusedGenBound0016
  | ⟨17, _⟩ => plane383UnusedGenBound0017
  | ⟨18, _⟩ => plane383UnusedGenBound0018
  | ⟨19, _⟩ => plane383UnusedGenBound0019
  | ⟨20, _⟩ => plane383UnusedGenBound0020
  | ⟨21, _⟩ => plane383UnusedGenBound0021
  | ⟨22, _⟩ => plane383UnusedGenBound0022
  | ⟨23, _⟩ => plane383UnusedGenBound0023
  | ⟨24, _⟩ => plane383UnusedGenBound0024
  | ⟨25, _⟩ => plane383UnusedGenBound0025
  | ⟨26, _⟩ => plane383UnusedGenBound0026
  | ⟨27, _⟩ => plane383UnusedGenBound0027
  | ⟨k + 28, h⟩ => by omega
theorem plane383UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (0 : Fin 19) = [257, 68, 32, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0001 (by decide)
theorem plane383UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (1 : Fin 19) = [259, 68, 34, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0002 (by decide)
theorem plane383UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (2 : Fin 19) = [258, 68, 35, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0003 (by decide)
theorem plane383UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (3 : Fin 19) = [261, 68, 36, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0004 (by decide)
theorem plane383UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (4 : Fin 19) = [263, 68, 38, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0005 (by decide)
theorem plane383UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (5 : Fin 19) = [262, 68, 39, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0006 (by decide)
theorem plane383UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (6 : Fin 19) = [289, 128, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0007 (by decide)
theorem plane383UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (7 : Fin 19) = [289, 129, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0008 (by decide)
theorem plane383UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (8 : Fin 19) = [289, 131, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0009 (by decide)
theorem plane383UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (9 : Fin 19) = [289, 133, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0010 (by decide)
theorem plane383UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (10 : Fin 19) = [289, 134, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0011 (by decide)
theorem plane383UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (11 : Fin 19) = [289, 135, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0012 (by decide)
theorem plane383UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (12 : Fin 19) = [289, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0013 (by decide)
theorem plane383UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (13 : Fin 19) = [289, 162, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0014 (by decide)
theorem plane383UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (14 : Fin 19) = [289, 163, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0015 (by decide)
theorem plane383UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (15 : Fin 19) = [289, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0016 (by decide)
theorem plane383UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (16 : Fin 19) = [289, 165, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0017 (by decide)
theorem plane383UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (17 : Fin 19) = [289, 166, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0018 (by decide)
theorem plane383UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane383UnusedGenDeadBasis (18 : Fin 19) = [289, 167, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane383UnusedGenSource0019 (by decide)
theorem plane383UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane383UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane383UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane383UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane383UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane383UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane383UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane383UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane383UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane383UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane383UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane383UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane383UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane383UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane383UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane383UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane383UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane383UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane383UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane383UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane383UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
