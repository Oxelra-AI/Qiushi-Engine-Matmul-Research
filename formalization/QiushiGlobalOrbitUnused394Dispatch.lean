import QiushiGlobalOrbitUnused394Bindings00
import QiushiGlobalOrbitUnused394Bindings01
import QiushiGlobalOrbitUnused394Bindings02
import QiushiGlobalOrbitUnused394Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane394UnusedGenSourceQRA (i : Fin 32) :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenSourceBasis i)) (plane394UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane394UnusedGenBound0000
  | ⟨1, _⟩ => plane394UnusedGenBound0001
  | ⟨2, _⟩ => plane394UnusedGenBound0002
  | ⟨3, _⟩ => plane394UnusedGenBound0003
  | ⟨4, _⟩ => plane394UnusedGenBound0004
  | ⟨5, _⟩ => plane394UnusedGenBound0005
  | ⟨6, _⟩ => plane394UnusedGenBound0006
  | ⟨7, _⟩ => plane394UnusedGenBound0007
  | ⟨8, _⟩ => plane394UnusedGenBound0008
  | ⟨9, _⟩ => plane394UnusedGenBound0009
  | ⟨10, _⟩ => plane394UnusedGenBound0010
  | ⟨11, _⟩ => plane394UnusedGenBound0011
  | ⟨12, _⟩ => plane394UnusedGenBound0012
  | ⟨13, _⟩ => plane394UnusedGenBound0013
  | ⟨14, _⟩ => plane394UnusedGenBound0014
  | ⟨15, _⟩ => plane394UnusedGenBound0015
  | ⟨16, _⟩ => plane394UnusedGenBound0016
  | ⟨17, _⟩ => plane394UnusedGenBound0017
  | ⟨18, _⟩ => plane394UnusedGenBound0018
  | ⟨19, _⟩ => plane394UnusedGenBound0019
  | ⟨20, _⟩ => plane394UnusedGenBound0020
  | ⟨21, _⟩ => plane394UnusedGenBound0021
  | ⟨22, _⟩ => plane394UnusedGenBound0022
  | ⟨23, _⟩ => plane394UnusedGenBound0023
  | ⟨24, _⟩ => plane394UnusedGenBound0024
  | ⟨25, _⟩ => plane394UnusedGenBound0025
  | ⟨26, _⟩ => plane394UnusedGenBound0026
  | ⟨27, _⟩ => plane394UnusedGenBound0027
  | ⟨28, _⟩ => plane394UnusedGenBound0028
  | ⟨29, _⟩ => plane394UnusedGenBound0029
  | ⟨30, _⟩ => plane394UnusedGenBound0030
  | ⟨31, _⟩ => plane394UnusedGenBound0031
  | ⟨k + 32, h⟩ => by omega
theorem plane394UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (0 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (0 : Fin 25) = [288, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0000 (by decide)
theorem plane394UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (1 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (1 : Fin 25) = [289, 68, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0001 (by decide)
theorem plane394UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (2 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (2 : Fin 25) = [257, 68, 32, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0004 (by decide)
theorem plane394UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (3 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (3 : Fin 25) = [259, 68, 34, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0005 (by decide)
theorem plane394UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (4 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (4 : Fin 25) = [258, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0006 (by decide)
theorem plane394UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (5 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (5 : Fin 25) = [261, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0007 (by decide)
theorem plane394UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (6 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (6 : Fin 25) = [263, 68, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0008 (by decide)
theorem plane394UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (7 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (7 : Fin 25) = [262, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0009 (by decide)
theorem plane394UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (8 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (8 : Fin 25) = [289, 128, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0010 (by decide)
theorem plane394UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (9 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (9 : Fin 25) = [289, 129, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0011 (by decide)
theorem plane394UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (10 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (10 : Fin 25) = [289, 131, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0012 (by decide)
theorem plane394UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (11 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (11 : Fin 25) = [289, 133, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0014 (by decide)
theorem plane394UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (12 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (12 : Fin 25) = [289, 134, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0015 (by decide)
theorem plane394UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (13 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (13 : Fin 25) = [289, 135, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0016 (by decide)
theorem plane394UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (14 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (14 : Fin 25) = [289, 160, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0017 (by decide)
theorem plane394UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (15 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (15 : Fin 25) = [289, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0018 (by decide)
theorem plane394UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (16 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (16 : Fin 25) = [289, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0019 (by decide)
theorem plane394UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (17 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (17 : Fin 25) = [289, 163, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0020 (by decide)
theorem plane394UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (18 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (18 : Fin 25) = [289, 164, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0021 (by decide)
theorem plane394UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (19 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (19 : Fin 25) = [289, 165, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0022 (by decide)
theorem plane394UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (20 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (20 : Fin 25) = [289, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0023 (by decide)
theorem plane394UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (21 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (21 : Fin 25) = [289, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0024 (by decide)
theorem plane394UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (22 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (22 : Fin 25) = [258, 128, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0027 (by decide)
theorem plane394UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (23 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (23 : Fin 25) = [258, 133, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0028 (by decide)
theorem plane394UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis (24 : Fin 25))) 16 := by
  rw [show plane394UnusedGenDeadBasis (24 : Fin 25) = [258, 135, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane394UnusedGenSource0029 (by decide)
theorem plane394UnusedGenDeadQRA (d : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane394UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane394UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane394UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane394UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane394UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane394UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane394UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane394UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane394UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane394UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane394UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane394UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane394UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane394UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane394UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane394UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane394UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane394UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane394UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane394UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane394UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane394UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane394UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane394UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane394UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane394UnusedGenDeadBound0024
  | ⟨k + 25, h⟩ => by omega
end QiushiMatmul
