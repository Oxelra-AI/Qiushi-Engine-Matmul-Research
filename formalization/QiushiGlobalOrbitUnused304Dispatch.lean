import QiushiGlobalOrbitUnused304Bindings00
import QiushiGlobalOrbitUnused304Bindings01
import QiushiGlobalOrbitUnused304Bindings02
import QiushiGlobalOrbitUnused304Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane304UnusedGenSourceQRA (i : Fin 35) :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenSourceBasis i)) (plane304UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane304UnusedGenBound0000
  | ⟨1, _⟩ => plane304UnusedGenBound0001
  | ⟨2, _⟩ => plane304UnusedGenBound0002
  | ⟨3, _⟩ => plane304UnusedGenBound0003
  | ⟨4, _⟩ => plane304UnusedGenBound0004
  | ⟨5, _⟩ => plane304UnusedGenBound0005
  | ⟨6, _⟩ => plane304UnusedGenBound0006
  | ⟨7, _⟩ => plane304UnusedGenBound0007
  | ⟨8, _⟩ => plane304UnusedGenBound0008
  | ⟨9, _⟩ => plane304UnusedGenBound0009
  | ⟨10, _⟩ => plane304UnusedGenBound0010
  | ⟨11, _⟩ => plane304UnusedGenBound0011
  | ⟨12, _⟩ => plane304UnusedGenBound0012
  | ⟨13, _⟩ => plane304UnusedGenBound0013
  | ⟨14, _⟩ => plane304UnusedGenBound0014
  | ⟨15, _⟩ => plane304UnusedGenBound0015
  | ⟨16, _⟩ => plane304UnusedGenBound0016
  | ⟨17, _⟩ => plane304UnusedGenBound0017
  | ⟨18, _⟩ => plane304UnusedGenBound0018
  | ⟨19, _⟩ => plane304UnusedGenBound0019
  | ⟨20, _⟩ => plane304UnusedGenBound0020
  | ⟨21, _⟩ => plane304UnusedGenBound0021
  | ⟨22, _⟩ => plane304UnusedGenBound0022
  | ⟨23, _⟩ => plane304UnusedGenBound0023
  | ⟨24, _⟩ => plane304UnusedGenBound0024
  | ⟨25, _⟩ => plane304UnusedGenBound0025
  | ⟨26, _⟩ => plane304UnusedGenBound0026
  | ⟨27, _⟩ => plane304UnusedGenBound0027
  | ⟨28, _⟩ => plane304UnusedGenBound0028
  | ⟨29, _⟩ => plane304UnusedGenBound0029
  | ⟨30, _⟩ => plane304UnusedGenBound0030
  | ⟨31, _⟩ => plane304UnusedGenBound0031
  | ⟨32, _⟩ => plane304UnusedGenBound0032
  | ⟨33, _⟩ => plane304UnusedGenBound0033
  | ⟨34, _⟩ => plane304UnusedGenBound0034
  | ⟨k + 35, h⟩ => by omega
theorem plane304UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (0 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (0 : Fin 34) = [256, 80, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0000 (by decide)
theorem plane304UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (1 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (1 : Fin 34) = [256, 82, 10, 6, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0001 (by decide)
theorem plane304UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (2 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (2 : Fin 34) = [256, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0002 (by decide)
theorem plane304UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (3 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (3 : Fin 34) = [256, 70, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0003 (by decide)
theorem plane304UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (4 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (4 : Fin 34) = [256, 64, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0004 (by decide)
theorem plane304UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (5 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (5 : Fin 34) = [256, 66, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0005 (by decide)
theorem plane304UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (6 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (6 : Fin 34) = [256, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0006 (by decide)
theorem plane304UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (7 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (7 : Fin 34) = [256, 84, 34, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0007 (by decide)
theorem plane304UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (8 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (8 : Fin 34) = [256, 84, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0008 (by decide)
theorem plane304UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (9 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (9 : Fin 34) = [256, 84, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0009 (by decide)
theorem plane304UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (10 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (10 : Fin 34) = [256, 84, 48, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0010 (by decide)
theorem plane304UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (11 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (11 : Fin 34) = [256, 84, 50, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0011 (by decide)
theorem plane304UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (12 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (12 : Fin 34) = [256, 84, 52, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0012 (by decide)
theorem plane304UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (13 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (13 : Fin 34) = [256, 84, 54, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0013 (by decide)
theorem plane304UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (14 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (14 : Fin 34) = [256, 128, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0014 (by decide)
theorem plane304UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (15 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (15 : Fin 34) = [256, 130, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0015 (by decide)
theorem plane304UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (16 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (16 : Fin 34) = [256, 132, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0016 (by decide)
theorem plane304UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (17 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (17 : Fin 34) = [256, 134, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0017 (by decide)
theorem plane304UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (18 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (18 : Fin 34) = [256, 144, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0018 (by decide)
theorem plane304UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (19 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (19 : Fin 34) = [256, 146, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0019 (by decide)
theorem plane304UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (20 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (20 : Fin 34) = [256, 148, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0020 (by decide)
theorem plane304UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (21 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (21 : Fin 34) = [256, 150, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0021 (by decide)
theorem plane304UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (22 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (22 : Fin 34) = [256, 162, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0022 (by decide)
theorem plane304UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (23 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (23 : Fin 34) = [256, 164, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0023 (by decide)
theorem plane304UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (24 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (24 : Fin 34) = [256, 166, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0024 (by decide)
theorem plane304UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (25 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (25 : Fin 34) = [256, 178, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0025 (by decide)
theorem plane304UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (26 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (26 : Fin 34) = [256, 180, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0026 (by decide)
theorem plane304UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (27 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (27 : Fin 34) = [256, 182, 84, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0027 (by decide)
theorem plane304UnusedGenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (28 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (28 : Fin 34) = [256, 80, 34, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0028 (by decide)
theorem plane304UnusedGenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (29 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (29 : Fin 34) = [256, 162, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0029 (by decide)
theorem plane304UnusedGenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (30 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (30 : Fin 34) = [256, 164, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0030 (by decide)
theorem plane304UnusedGenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (31 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (31 : Fin 34) = [256, 164, 70, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0031 (by decide)
theorem plane304UnusedGenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (32 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (32 : Fin 34) = [256, 166, 70, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0032 (by decide)
theorem plane304UnusedGenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis (33 : Fin 34))) 15 := by
  rw [show plane304UnusedGenDeadBasis (33 : Fin 34) = [256, 130, 64, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane304UnusedGenSource0033 (by decide)
theorem plane304UnusedGenDeadQRA (d : Fin 34) :
    QuotientRankAtLeast (spanCodes (plane304UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane304UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane304UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane304UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane304UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane304UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane304UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane304UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane304UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane304UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane304UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane304UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane304UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane304UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane304UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane304UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane304UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane304UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane304UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane304UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane304UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane304UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane304UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane304UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane304UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane304UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane304UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane304UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane304UnusedGenDeadBound0027
  | ⟨28, _⟩ => plane304UnusedGenDeadBound0028
  | ⟨29, _⟩ => plane304UnusedGenDeadBound0029
  | ⟨30, _⟩ => plane304UnusedGenDeadBound0030
  | ⟨31, _⟩ => plane304UnusedGenDeadBound0031
  | ⟨32, _⟩ => plane304UnusedGenDeadBound0032
  | ⟨33, _⟩ => plane304UnusedGenDeadBound0033
  | ⟨k + 34, h⟩ => by omega
end QiushiMatmul
