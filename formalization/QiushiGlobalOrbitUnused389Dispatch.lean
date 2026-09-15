import QiushiGlobalOrbitUnused389Bindings00
import QiushiGlobalOrbitUnused389Bindings01
import QiushiGlobalOrbitUnused389Bindings02
import QiushiGlobalOrbitUnused389Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane389UnusedGenSourceQRA (i : Fin 35) :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenSourceBasis i)) (plane389UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane389UnusedGenBound0000
  | ⟨1, _⟩ => plane389UnusedGenBound0001
  | ⟨2, _⟩ => plane389UnusedGenBound0002
  | ⟨3, _⟩ => plane389UnusedGenBound0003
  | ⟨4, _⟩ => plane389UnusedGenBound0004
  | ⟨5, _⟩ => plane389UnusedGenBound0005
  | ⟨6, _⟩ => plane389UnusedGenBound0006
  | ⟨7, _⟩ => plane389UnusedGenBound0007
  | ⟨8, _⟩ => plane389UnusedGenBound0008
  | ⟨9, _⟩ => plane389UnusedGenBound0009
  | ⟨10, _⟩ => plane389UnusedGenBound0010
  | ⟨11, _⟩ => plane389UnusedGenBound0011
  | ⟨12, _⟩ => plane389UnusedGenBound0012
  | ⟨13, _⟩ => plane389UnusedGenBound0013
  | ⟨14, _⟩ => plane389UnusedGenBound0014
  | ⟨15, _⟩ => plane389UnusedGenBound0015
  | ⟨16, _⟩ => plane389UnusedGenBound0016
  | ⟨17, _⟩ => plane389UnusedGenBound0017
  | ⟨18, _⟩ => plane389UnusedGenBound0018
  | ⟨19, _⟩ => plane389UnusedGenBound0019
  | ⟨20, _⟩ => plane389UnusedGenBound0020
  | ⟨21, _⟩ => plane389UnusedGenBound0021
  | ⟨22, _⟩ => plane389UnusedGenBound0022
  | ⟨23, _⟩ => plane389UnusedGenBound0023
  | ⟨24, _⟩ => plane389UnusedGenBound0024
  | ⟨25, _⟩ => plane389UnusedGenBound0025
  | ⟨26, _⟩ => plane389UnusedGenBound0026
  | ⟨27, _⟩ => plane389UnusedGenBound0027
  | ⟨28, _⟩ => plane389UnusedGenBound0028
  | ⟨29, _⟩ => plane389UnusedGenBound0029
  | ⟨30, _⟩ => plane389UnusedGenBound0030
  | ⟨31, _⟩ => plane389UnusedGenBound0031
  | ⟨32, _⟩ => plane389UnusedGenBound0032
  | ⟨33, _⟩ => plane389UnusedGenBound0033
  | ⟨34, _⟩ => plane389UnusedGenBound0034
  | ⟨k + 35, h⟩ => by omega
theorem plane389UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (0 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (0 : Fin 24) = [166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0000 (by decide)
theorem plane389UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (1 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (1 : Fin 24) = [133, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0002 (by decide)
theorem plane389UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (2 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (2 : Fin 24) = [131, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0003 (by decide)
theorem plane389UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (3 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (3 : Fin 24) = [256, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0004 (by decide)
theorem plane389UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (4 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (4 : Fin 24) = [257, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0005 (by decide)
theorem plane389UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (5 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (5 : Fin 24) = [258, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0006 (by decide)
theorem plane389UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (6 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (6 : Fin 24) = [261, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0008 (by decide)
theorem plane389UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (7 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (7 : Fin 24) = [262, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0009 (by decide)
theorem plane389UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (8 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (8 : Fin 24) = [263, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0010 (by decide)
theorem plane389UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (9 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (9 : Fin 24) = [288, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0011 (by decide)
theorem plane389UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (10 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (10 : Fin 24) = [289, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0012 (by decide)
theorem plane389UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (11 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (11 : Fin 24) = [290, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0013 (by decide)
theorem plane389UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (12 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (12 : Fin 24) = [291, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0014 (by decide)
theorem plane389UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (13 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (13 : Fin 24) = [292, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0015 (by decide)
theorem plane389UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (14 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (14 : Fin 24) = [293, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0016 (by decide)
theorem plane389UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (15 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (15 : Fin 24) = [294, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0017 (by decide)
theorem plane389UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (16 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (16 : Fin 24) = [295, 166, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0018 (by decide)
theorem plane389UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (17 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (17 : Fin 24) = [262, 166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0019 (by decide)
theorem plane389UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (18 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (18 : Fin 24) = [258, 133, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0021 (by decide)
theorem plane389UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (19 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (19 : Fin 24) = [262, 133, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0022 (by decide)
theorem plane389UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (20 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (20 : Fin 24) = [263, 133, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0023 (by decide)
theorem plane389UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (21 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (21 : Fin 24) = [258, 131, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0024 (by decide)
theorem plane389UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (22 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (22 : Fin 24) = [262, 131, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0025 (by decide)
theorem plane389UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis (23 : Fin 24))) 16 := by
  rw [show plane389UnusedGenDeadBasis (23 : Fin 24) = [263, 131, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane389UnusedGenSource0026 (by decide)
theorem plane389UnusedGenDeadQRA (d : Fin 24) :
    QuotientRankAtLeast (spanCodes (plane389UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane389UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane389UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane389UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane389UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane389UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane389UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane389UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane389UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane389UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane389UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane389UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane389UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane389UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane389UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane389UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane389UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane389UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane389UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane389UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane389UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane389UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane389UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane389UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane389UnusedGenDeadBound0023
  | ⟨k + 24, h⟩ => by omega
end QiushiMatmul
