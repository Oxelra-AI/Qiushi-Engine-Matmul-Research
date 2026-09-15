import QiushiGlobalOrbitUnused337Bindings00
import QiushiGlobalOrbitUnused337Bindings01
import QiushiGlobalOrbitUnused337Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane337UnusedGenSourceQRA (i : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenSourceBasis i)) (plane337UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane337UnusedGenBound0000
  | ⟨1, _⟩ => plane337UnusedGenBound0001
  | ⟨2, _⟩ => plane337UnusedGenBound0002
  | ⟨3, _⟩ => plane337UnusedGenBound0003
  | ⟨4, _⟩ => plane337UnusedGenBound0004
  | ⟨5, _⟩ => plane337UnusedGenBound0005
  | ⟨6, _⟩ => plane337UnusedGenBound0006
  | ⟨7, _⟩ => plane337UnusedGenBound0007
  | ⟨8, _⟩ => plane337UnusedGenBound0008
  | ⟨9, _⟩ => plane337UnusedGenBound0009
  | ⟨10, _⟩ => plane337UnusedGenBound0010
  | ⟨11, _⟩ => plane337UnusedGenBound0011
  | ⟨12, _⟩ => plane337UnusedGenBound0012
  | ⟨13, _⟩ => plane337UnusedGenBound0013
  | ⟨14, _⟩ => plane337UnusedGenBound0014
  | ⟨15, _⟩ => plane337UnusedGenBound0015
  | ⟨16, _⟩ => plane337UnusedGenBound0016
  | ⟨17, _⟩ => plane337UnusedGenBound0017
  | ⟨18, _⟩ => plane337UnusedGenBound0018
  | ⟨19, _⟩ => plane337UnusedGenBound0019
  | ⟨20, _⟩ => plane337UnusedGenBound0020
  | ⟨21, _⟩ => plane337UnusedGenBound0021
  | ⟨22, _⟩ => plane337UnusedGenBound0022
  | ⟨23, _⟩ => plane337UnusedGenBound0023
  | ⟨24, _⟩ => plane337UnusedGenBound0024
  | ⟨25, _⟩ => plane337UnusedGenBound0025
  | ⟨26, _⟩ => plane337UnusedGenBound0026
  | ⟨27, _⟩ => plane337UnusedGenBound0027
  | ⟨28, _⟩ => plane337UnusedGenBound0028
  | ⟨29, _⟩ => plane337UnusedGenBound0029
  | ⟨k + 30, h⟩ => by omega
theorem plane337UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (0 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (0 : Fin 27) = [258, 98, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0000 (by decide)
theorem plane337UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (1 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (1 : Fin 27) = [258, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0001 (by decide)
theorem plane337UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (2 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (2 : Fin 27) = [258, 98, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0002 (by decide)
theorem plane337UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (3 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (3 : Fin 27) = [258, 98, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0003 (by decide)
theorem plane337UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (4 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (4 : Fin 27) = [258, 70, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0004 (by decide)
theorem plane337UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (5 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (5 : Fin 27) = [258, 74, 40, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0005 (by decide)
theorem plane337UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (6 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (6 : Fin 27) = [258, 72, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0006 (by decide)
theorem plane337UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (7 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (7 : Fin 27) = [258, 78, 44, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0007 (by decide)
theorem plane337UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (8 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (8 : Fin 27) = [258, 76, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0008 (by decide)
theorem plane337UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (9 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (9 : Fin 27) = [258, 128, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0009 (by decide)
theorem plane337UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (10 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (10 : Fin 27) = [258, 132, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0010 (by decide)
theorem plane337UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (11 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (11 : Fin 27) = [258, 136, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0011 (by decide)
theorem plane337UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (12 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (12 : Fin 27) = [258, 138, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0012 (by decide)
theorem plane337UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (13 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (13 : Fin 27) = [258, 140, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0013 (by decide)
theorem plane337UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (14 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (14 : Fin 27) = [258, 142, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0014 (by decide)
theorem plane337UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (15 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (15 : Fin 27) = [258, 162, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0015 (by decide)
theorem plane337UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (16 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (16 : Fin 27) = [258, 164, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0016 (by decide)
theorem plane337UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (17 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (17 : Fin 27) = [258, 166, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0017 (by decide)
theorem plane337UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (18 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (18 : Fin 27) = [258, 168, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0018 (by decide)
theorem plane337UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (19 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (19 : Fin 27) = [258, 170, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0019 (by decide)
theorem plane337UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (20 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (20 : Fin 27) = [258, 172, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0020 (by decide)
theorem plane337UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (21 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (21 : Fin 27) = [258, 174, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0021 (by decide)
theorem plane337UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (22 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (22 : Fin 27) = [258, 74, 40, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0023 (by decide)
theorem plane337UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (23 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (23 : Fin 27) = [258, 134, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0025 (by decide)
theorem plane337UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (24 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (24 : Fin 27) = [258, 164, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0026 (by decide)
theorem plane337UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (25 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (25 : Fin 27) = [258, 166, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0027 (by decide)
theorem plane337UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis (26 : Fin 27))) 15 := by
  rw [show plane337UnusedGenDeadBasis (26 : Fin 27) = [258, 128, 72, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane337UnusedGenSource0029 (by decide)
theorem plane337UnusedGenDeadQRA (d : Fin 27) :
    QuotientRankAtLeast (spanCodes (plane337UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane337UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane337UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane337UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane337UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane337UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane337UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane337UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane337UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane337UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane337UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane337UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane337UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane337UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane337UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane337UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane337UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane337UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane337UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane337UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane337UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane337UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane337UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane337UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane337UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane337UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane337UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane337UnusedGenDeadBound0026
  | ⟨k + 27, h⟩ => by omega
end QiushiMatmul
