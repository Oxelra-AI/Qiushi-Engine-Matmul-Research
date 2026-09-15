import QiushiGlobalOrbitUnused333Bindings00
import QiushiGlobalOrbitUnused333Bindings01
import QiushiGlobalOrbitUnused333Bindings02
import QiushiGlobalOrbitUnused333Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane333UnusedGenSourceQRA (i : Fin 36) :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenSourceBasis i)) (plane333UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane333UnusedGenBound0000
  | ⟨1, _⟩ => plane333UnusedGenBound0001
  | ⟨2, _⟩ => plane333UnusedGenBound0002
  | ⟨3, _⟩ => plane333UnusedGenBound0003
  | ⟨4, _⟩ => plane333UnusedGenBound0004
  | ⟨5, _⟩ => plane333UnusedGenBound0005
  | ⟨6, _⟩ => plane333UnusedGenBound0006
  | ⟨7, _⟩ => plane333UnusedGenBound0007
  | ⟨8, _⟩ => plane333UnusedGenBound0008
  | ⟨9, _⟩ => plane333UnusedGenBound0009
  | ⟨10, _⟩ => plane333UnusedGenBound0010
  | ⟨11, _⟩ => plane333UnusedGenBound0011
  | ⟨12, _⟩ => plane333UnusedGenBound0012
  | ⟨13, _⟩ => plane333UnusedGenBound0013
  | ⟨14, _⟩ => plane333UnusedGenBound0014
  | ⟨15, _⟩ => plane333UnusedGenBound0015
  | ⟨16, _⟩ => plane333UnusedGenBound0016
  | ⟨17, _⟩ => plane333UnusedGenBound0017
  | ⟨18, _⟩ => plane333UnusedGenBound0018
  | ⟨19, _⟩ => plane333UnusedGenBound0019
  | ⟨20, _⟩ => plane333UnusedGenBound0020
  | ⟨21, _⟩ => plane333UnusedGenBound0021
  | ⟨22, _⟩ => plane333UnusedGenBound0022
  | ⟨23, _⟩ => plane333UnusedGenBound0023
  | ⟨24, _⟩ => plane333UnusedGenBound0024
  | ⟨25, _⟩ => plane333UnusedGenBound0025
  | ⟨26, _⟩ => plane333UnusedGenBound0026
  | ⟨27, _⟩ => plane333UnusedGenBound0027
  | ⟨28, _⟩ => plane333UnusedGenBound0028
  | ⟨29, _⟩ => plane333UnusedGenBound0029
  | ⟨30, _⟩ => plane333UnusedGenBound0030
  | ⟨31, _⟩ => plane333UnusedGenBound0031
  | ⟨32, _⟩ => plane333UnusedGenBound0032
  | ⟨33, _⟩ => plane333UnusedGenBound0033
  | ⟨34, _⟩ => plane333UnusedGenBound0034
  | ⟨35, _⟩ => plane333UnusedGenBound0035
  | ⟨k + 36, h⟩ => by omega
theorem plane333UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (0 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (0 : Fin 29) = [298, 96, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0000 (by decide)
theorem plane333UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (1 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (1 : Fin 29) = [290, 96, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0001 (by decide)
theorem plane333UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (2 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (2 : Fin 29) = [294, 96, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0002 (by decide)
theorem plane333UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (3 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (3 : Fin 29) = [264, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0004 (by decide)
theorem plane333UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (4 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (4 : Fin 29) = [270, 68, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0005 (by decide)
theorem plane333UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (5 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (5 : Fin 29) = [268, 70, 38, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0006 (by decide)
theorem plane333UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (6 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (6 : Fin 29) = [256, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0008 (by decide)
theorem plane333UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (7 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (7 : Fin 29) = [262, 76, 44, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0009 (by decide)
theorem plane333UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (8 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (8 : Fin 29) = [260, 78, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0010 (by decide)
theorem plane333UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (9 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (9 : Fin 29) = [298, 128, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0011 (by decide)
theorem plane333UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (10 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (10 : Fin 29) = [298, 136, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0012 (by decide)
theorem plane333UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (11 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (11 : Fin 29) = [298, 142, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0013 (by decide)
theorem plane333UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (12 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (12 : Fin 29) = [298, 160, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0014 (by decide)
theorem plane333UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (13 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (13 : Fin 29) = [298, 162, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0015 (by decide)
theorem plane333UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (14 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (14 : Fin 29) = [298, 164, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0016 (by decide)
theorem plane333UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (15 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (15 : Fin 29) = [298, 168, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0017 (by decide)
theorem plane333UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (16 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (16 : Fin 29) = [298, 170, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0018 (by decide)
theorem plane333UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (17 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (17 : Fin 29) = [298, 172, 96, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0019 (by decide)
theorem plane333UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (18 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (18 : Fin 29) = [290, 96, 16, 8, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0020 (by decide)
theorem plane333UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (19 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (19 : Fin 29) = [262, 68, 36, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0022 (by decide)
theorem plane333UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (20 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (20 : Fin 29) = [290, 128, 96, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0023 (by decide)
theorem plane333UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (21 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (21 : Fin 29) = [290, 160, 96, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0024 (by decide)
theorem plane333UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (22 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (22 : Fin 29) = [294, 132, 96, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0025 (by decide)
theorem plane333UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (23 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (23 : Fin 29) = [294, 162, 96, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0026 (by decide)
theorem plane333UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (24 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (24 : Fin 29) = [294, 166, 96, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0027 (by decide)
theorem plane333UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (25 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (25 : Fin 29) = [264, 132, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0029 (by decide)
theorem plane333UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (26 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (26 : Fin 29) = [268, 136, 70, 38, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0030 (by decide)
theorem plane333UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (27 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (27 : Fin 29) = [256, 132, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0031 (by decide)
theorem plane333UnusedGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis (28 : Fin 29))) 15 := by
  rw [show plane333UnusedGenDeadBasis (28 : Fin 29) = [260, 136, 78, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane333UnusedGenSource0032 (by decide)
theorem plane333UnusedGenDeadQRA (d : Fin 29) :
    QuotientRankAtLeast (spanCodes (plane333UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane333UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane333UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane333UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane333UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane333UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane333UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane333UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane333UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane333UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane333UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane333UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane333UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane333UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane333UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane333UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane333UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane333UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane333UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane333UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane333UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane333UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane333UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane333UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane333UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane333UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane333UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane333UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane333UnusedGenDeadBound0027
  | ⟨28, _⟩ => plane333UnusedGenDeadBound0028
  | ⟨k + 29, h⟩ => by omega
end QiushiMatmul
