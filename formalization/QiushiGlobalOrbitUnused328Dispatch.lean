import QiushiGlobalOrbitUnused328Bindings00
import QiushiGlobalOrbitUnused328Bindings01
import QiushiGlobalOrbitUnused328Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane328UnusedGenSourceQRA (i : Fin 29) :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenSourceBasis i)) (plane328UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane328UnusedGenBound0000
  | ⟨1, _⟩ => plane328UnusedGenBound0001
  | ⟨2, _⟩ => plane328UnusedGenBound0002
  | ⟨3, _⟩ => plane328UnusedGenBound0003
  | ⟨4, _⟩ => plane328UnusedGenBound0004
  | ⟨5, _⟩ => plane328UnusedGenBound0005
  | ⟨6, _⟩ => plane328UnusedGenBound0006
  | ⟨7, _⟩ => plane328UnusedGenBound0007
  | ⟨8, _⟩ => plane328UnusedGenBound0008
  | ⟨9, _⟩ => plane328UnusedGenBound0009
  | ⟨10, _⟩ => plane328UnusedGenBound0010
  | ⟨11, _⟩ => plane328UnusedGenBound0011
  | ⟨12, _⟩ => plane328UnusedGenBound0012
  | ⟨13, _⟩ => plane328UnusedGenBound0013
  | ⟨14, _⟩ => plane328UnusedGenBound0014
  | ⟨15, _⟩ => plane328UnusedGenBound0015
  | ⟨16, _⟩ => plane328UnusedGenBound0016
  | ⟨17, _⟩ => plane328UnusedGenBound0017
  | ⟨18, _⟩ => plane328UnusedGenBound0018
  | ⟨19, _⟩ => plane328UnusedGenBound0019
  | ⟨20, _⟩ => plane328UnusedGenBound0020
  | ⟨21, _⟩ => plane328UnusedGenBound0021
  | ⟨22, _⟩ => plane328UnusedGenBound0022
  | ⟨23, _⟩ => plane328UnusedGenBound0023
  | ⟨24, _⟩ => plane328UnusedGenBound0024
  | ⟨25, _⟩ => plane328UnusedGenBound0025
  | ⟨26, _⟩ => plane328UnusedGenBound0026
  | ⟨27, _⟩ => plane328UnusedGenBound0027
  | ⟨28, _⟩ => plane328UnusedGenBound0028
  | ⟨k + 29, h⟩ => by omega
theorem plane328UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (0 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (0 : Fin 25) = [140, 96, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0000 (by decide)
theorem plane328UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (1 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (1 : Fin 25) = [132, 96, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0001 (by decide)
theorem plane328UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (2 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (2 : Fin 25) = [134, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0002 (by decide)
theorem plane328UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (3 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (3 : Fin 25) = [140, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0004 (by decide)
theorem plane328UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (4 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (4 : Fin 25) = [140, 68, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0005 (by decide)
theorem plane328UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (5 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (5 : Fin 25) = [140, 70, 38, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0006 (by decide)
theorem plane328UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (6 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (6 : Fin 25) = [140, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0008 (by decide)
theorem plane328UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (7 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (7 : Fin 25) = [140, 76, 44, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0009 (by decide)
theorem plane328UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (8 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (8 : Fin 25) = [140, 78, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0010 (by decide)
theorem plane328UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (9 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (9 : Fin 25) = [256, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0011 (by decide)
theorem plane328UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (10 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (10 : Fin 25) = [258, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0012 (by decide)
theorem plane328UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (11 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (11 : Fin 25) = [260, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0013 (by decide)
theorem plane328UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (12 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (12 : Fin 25) = [262, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0014 (by decide)
theorem plane328UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (13 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (13 : Fin 25) = [264, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0015 (by decide)
theorem plane328UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (14 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (14 : Fin 25) = [266, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0016 (by decide)
theorem plane328UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (15 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (15 : Fin 25) = [268, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0017 (by decide)
theorem plane328UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (16 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (16 : Fin 25) = [270, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0018 (by decide)
theorem plane328UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (17 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (17 : Fin 25) = [292, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0019 (by decide)
theorem plane328UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (18 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (18 : Fin 25) = [294, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0020 (by decide)
theorem plane328UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (19 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (19 : Fin 25) = [300, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0021 (by decide)
theorem plane328UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (20 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (20 : Fin 25) = [302, 140, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0022 (by decide)
theorem plane328UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (21 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (21 : Fin 25) = [132, 96, 16, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0023 (by decide)
theorem plane328UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (22 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (22 : Fin 25) = [260, 134, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0024 (by decide)
theorem plane328UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (23 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (23 : Fin 25) = [262, 134, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0025 (by decide)
theorem plane328UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis (24 : Fin 25))) 15 := by
  rw [show plane328UnusedGenDeadBasis (24 : Fin 25) = [290, 134, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane328UnusedGenSource0026 (by decide)
theorem plane328UnusedGenDeadQRA (d : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane328UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane328UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane328UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane328UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane328UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane328UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane328UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane328UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane328UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane328UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane328UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane328UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane328UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane328UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane328UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane328UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane328UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane328UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane328UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane328UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane328UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane328UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane328UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane328UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane328UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane328UnusedGenDeadBound0024
  | ⟨k + 25, h⟩ => by omega
end QiushiMatmul
