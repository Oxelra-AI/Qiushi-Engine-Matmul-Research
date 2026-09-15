import QiushiGlobalOrbitUnused387Bindings00
import QiushiGlobalOrbitUnused387Bindings01
import QiushiGlobalOrbitUnused387Bindings02
import QiushiGlobalOrbitUnused387Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane387UnusedGenSourceQRA (i : Fin 32) :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenSourceBasis i)) (plane387UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane387UnusedGenBound0000
  | ⟨1, _⟩ => plane387UnusedGenBound0001
  | ⟨2, _⟩ => plane387UnusedGenBound0002
  | ⟨3, _⟩ => plane387UnusedGenBound0003
  | ⟨4, _⟩ => plane387UnusedGenBound0004
  | ⟨5, _⟩ => plane387UnusedGenBound0005
  | ⟨6, _⟩ => plane387UnusedGenBound0006
  | ⟨7, _⟩ => plane387UnusedGenBound0007
  | ⟨8, _⟩ => plane387UnusedGenBound0008
  | ⟨9, _⟩ => plane387UnusedGenBound0009
  | ⟨10, _⟩ => plane387UnusedGenBound0010
  | ⟨11, _⟩ => plane387UnusedGenBound0011
  | ⟨12, _⟩ => plane387UnusedGenBound0012
  | ⟨13, _⟩ => plane387UnusedGenBound0013
  | ⟨14, _⟩ => plane387UnusedGenBound0014
  | ⟨15, _⟩ => plane387UnusedGenBound0015
  | ⟨16, _⟩ => plane387UnusedGenBound0016
  | ⟨17, _⟩ => plane387UnusedGenBound0017
  | ⟨18, _⟩ => plane387UnusedGenBound0018
  | ⟨19, _⟩ => plane387UnusedGenBound0019
  | ⟨20, _⟩ => plane387UnusedGenBound0020
  | ⟨21, _⟩ => plane387UnusedGenBound0021
  | ⟨22, _⟩ => plane387UnusedGenBound0022
  | ⟨23, _⟩ => plane387UnusedGenBound0023
  | ⟨24, _⟩ => plane387UnusedGenBound0024
  | ⟨25, _⟩ => plane387UnusedGenBound0025
  | ⟨26, _⟩ => plane387UnusedGenBound0026
  | ⟨27, _⟩ => plane387UnusedGenBound0027
  | ⟨28, _⟩ => plane387UnusedGenBound0028
  | ⟨29, _⟩ => plane387UnusedGenBound0029
  | ⟨30, _⟩ => plane387UnusedGenBound0030
  | ⟨31, _⟩ => plane387UnusedGenBound0031
  | ⟨k + 32, h⟩ => by omega
theorem plane387UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (0 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (0 : Fin 20) = [162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0000 (by decide)
theorem plane387UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (1 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (1 : Fin 20) = [131, 68, 33, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0003 (by decide)
theorem plane387UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (2 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (2 : Fin 20) = [129, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0004 (by decide)
theorem plane387UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (3 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (3 : Fin 20) = [135, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0005 (by decide)
theorem plane387UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (4 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (4 : Fin 20) = [133, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0006 (by decide)
theorem plane387UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (5 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (5 : Fin 20) = [257, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0007 (by decide)
theorem plane387UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (6 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (6 : Fin 20) = [258, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0008 (by decide)
theorem plane387UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (7 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (7 : Fin 20) = [259, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0009 (by decide)
theorem plane387UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (8 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (8 : Fin 20) = [261, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0010 (by decide)
theorem plane387UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (9 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (9 : Fin 20) = [262, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0011 (by decide)
theorem plane387UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (10 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (10 : Fin 20) = [263, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0012 (by decide)
theorem plane387UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (11 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (11 : Fin 20) = [288, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0013 (by decide)
theorem plane387UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (12 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (12 : Fin 20) = [289, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0014 (by decide)
theorem plane387UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (13 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (13 : Fin 20) = [290, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0015 (by decide)
theorem plane387UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (14 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (14 : Fin 20) = [291, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0016 (by decide)
theorem plane387UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (15 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (15 : Fin 20) = [293, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0017 (by decide)
theorem plane387UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (16 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (16 : Fin 20) = [295, 162, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0018 (by decide)
theorem plane387UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (17 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (17 : Fin 20) = [258, 162, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0019 (by decide)
theorem plane387UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (18 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (18 : Fin 20) = [258, 135, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0022 (by decide)
theorem plane387UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis (19 : Fin 20))) 16 := by
  rw [show plane387UnusedGenDeadBasis (19 : Fin 20) = [258, 133, 68, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane387UnusedGenSource0023 (by decide)
theorem plane387UnusedGenDeadQRA (d : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane387UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane387UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane387UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane387UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane387UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane387UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane387UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane387UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane387UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane387UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane387UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane387UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane387UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane387UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane387UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane387UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane387UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane387UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane387UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane387UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane387UnusedGenDeadBound0019
  | ⟨k + 20, h⟩ => by omega
end QiushiMatmul
