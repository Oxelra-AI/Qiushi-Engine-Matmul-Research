import QiushiGlobalOrbitUnused401Bindings00
import QiushiGlobalOrbitUnused401Bindings01
import QiushiGlobalOrbitUnused401Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane401UnusedGenSourceQRA (i : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenSourceBasis i)) (plane401UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane401UnusedGenBound0000
  | ⟨1, _⟩ => plane401UnusedGenBound0001
  | ⟨2, _⟩ => plane401UnusedGenBound0002
  | ⟨3, _⟩ => plane401UnusedGenBound0003
  | ⟨4, _⟩ => plane401UnusedGenBound0004
  | ⟨5, _⟩ => plane401UnusedGenBound0005
  | ⟨6, _⟩ => plane401UnusedGenBound0006
  | ⟨7, _⟩ => plane401UnusedGenBound0007
  | ⟨8, _⟩ => plane401UnusedGenBound0008
  | ⟨9, _⟩ => plane401UnusedGenBound0009
  | ⟨10, _⟩ => plane401UnusedGenBound0010
  | ⟨11, _⟩ => plane401UnusedGenBound0011
  | ⟨12, _⟩ => plane401UnusedGenBound0012
  | ⟨13, _⟩ => plane401UnusedGenBound0013
  | ⟨14, _⟩ => plane401UnusedGenBound0014
  | ⟨15, _⟩ => plane401UnusedGenBound0015
  | ⟨16, _⟩ => plane401UnusedGenBound0016
  | ⟨17, _⟩ => plane401UnusedGenBound0017
  | ⟨18, _⟩ => plane401UnusedGenBound0018
  | ⟨19, _⟩ => plane401UnusedGenBound0019
  | ⟨20, _⟩ => plane401UnusedGenBound0020
  | ⟨21, _⟩ => plane401UnusedGenBound0021
  | ⟨22, _⟩ => plane401UnusedGenBound0022
  | ⟨23, _⟩ => plane401UnusedGenBound0023
  | ⟨24, _⟩ => plane401UnusedGenBound0024
  | ⟨25, _⟩ => plane401UnusedGenBound0025
  | ⟨26, _⟩ => plane401UnusedGenBound0026
  | ⟨27, _⟩ => plane401UnusedGenBound0027
  | ⟨28, _⟩ => plane401UnusedGenBound0028
  | ⟨29, _⟩ => plane401UnusedGenBound0029
  | ⟨k + 30, h⟩ => by omega
theorem plane401UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (0 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (0 : Fin 23) = [260, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0000 (by decide)
theorem plane401UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (1 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (1 : Fin 23) = [261, 96, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0001 (by decide)
theorem plane401UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (2 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (2 : Fin 23) = [257, 96, 16, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0002 (by decide)
theorem plane401UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (3 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (3 : Fin 23) = [261, 67, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0005 (by decide)
theorem plane401UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (4 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (4 : Fin 23) = [261, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0006 (by decide)
theorem plane401UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (5 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (5 : Fin 23) = [261, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0007 (by decide)
theorem plane401UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (6 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (6 : Fin 23) = [261, 70, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0008 (by decide)
theorem plane401UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (7 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (7 : Fin 23) = [261, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0009 (by decide)
theorem plane401UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (8 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (8 : Fin 23) = [261, 128, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0010 (by decide)
theorem plane401UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (9 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (9 : Fin 23) = [261, 129, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0011 (by decide)
theorem plane401UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (10 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (10 : Fin 23) = [261, 130, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0012 (by decide)
theorem plane401UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (11 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (11 : Fin 23) = [261, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0013 (by decide)
theorem plane401UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (12 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (12 : Fin 23) = [261, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0014 (by decide)
theorem plane401UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (13 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (13 : Fin 23) = [261, 134, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0015 (by decide)
theorem plane401UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (14 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (14 : Fin 23) = [261, 135, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0016 (by decide)
theorem plane401UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (15 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (15 : Fin 23) = [261, 160, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0017 (by decide)
theorem plane401UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (16 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (16 : Fin 23) = [261, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0018 (by decide)
theorem plane401UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (17 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (17 : Fin 23) = [261, 162, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0019 (by decide)
theorem plane401UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (18 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (18 : Fin 23) = [261, 163, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0020 (by decide)
theorem plane401UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (19 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (19 : Fin 23) = [261, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0021 (by decide)
theorem plane401UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (20 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (20 : Fin 23) = [261, 166, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0022 (by decide)
theorem plane401UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (21 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (21 : Fin 23) = [261, 167, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0023 (by decide)
theorem plane401UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis (22 : Fin 23))) 16 := by
  rw [show plane401UnusedGenDeadBasis (22 : Fin 23) = [261, 135, 67, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane401UnusedGenSource0026 (by decide)
theorem plane401UnusedGenDeadQRA (d : Fin 23) :
    QuotientRankAtLeast (spanCodes (plane401UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane401UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane401UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane401UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane401UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane401UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane401UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane401UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane401UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane401UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane401UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane401UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane401UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane401UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane401UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane401UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane401UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane401UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane401UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane401UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane401UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane401UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane401UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane401UnusedGenDeadBound0022
  | ⟨k + 23, h⟩ => by omega
end QiushiMatmul
