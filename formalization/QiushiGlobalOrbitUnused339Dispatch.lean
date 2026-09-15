import QiushiGlobalOrbitUnused339Bindings00
import QiushiGlobalOrbitUnused339Bindings01
import QiushiGlobalOrbitUnused339Bindings02
import QiushiGlobalOrbitUnused339Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane339UnusedGenSourceQRA (i : Fin 31) :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenSourceBasis i)) (plane339UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane339UnusedGenBound0000
  | ⟨1, _⟩ => plane339UnusedGenBound0001
  | ⟨2, _⟩ => plane339UnusedGenBound0002
  | ⟨3, _⟩ => plane339UnusedGenBound0003
  | ⟨4, _⟩ => plane339UnusedGenBound0004
  | ⟨5, _⟩ => plane339UnusedGenBound0005
  | ⟨6, _⟩ => plane339UnusedGenBound0006
  | ⟨7, _⟩ => plane339UnusedGenBound0007
  | ⟨8, _⟩ => plane339UnusedGenBound0008
  | ⟨9, _⟩ => plane339UnusedGenBound0009
  | ⟨10, _⟩ => plane339UnusedGenBound0010
  | ⟨11, _⟩ => plane339UnusedGenBound0011
  | ⟨12, _⟩ => plane339UnusedGenBound0012
  | ⟨13, _⟩ => plane339UnusedGenBound0013
  | ⟨14, _⟩ => plane339UnusedGenBound0014
  | ⟨15, _⟩ => plane339UnusedGenBound0015
  | ⟨16, _⟩ => plane339UnusedGenBound0016
  | ⟨17, _⟩ => plane339UnusedGenBound0017
  | ⟨18, _⟩ => plane339UnusedGenBound0018
  | ⟨19, _⟩ => plane339UnusedGenBound0019
  | ⟨20, _⟩ => plane339UnusedGenBound0020
  | ⟨21, _⟩ => plane339UnusedGenBound0021
  | ⟨22, _⟩ => plane339UnusedGenBound0022
  | ⟨23, _⟩ => plane339UnusedGenBound0023
  | ⟨24, _⟩ => plane339UnusedGenBound0024
  | ⟨25, _⟩ => plane339UnusedGenBound0025
  | ⟨26, _⟩ => plane339UnusedGenBound0026
  | ⟨27, _⟩ => plane339UnusedGenBound0027
  | ⟨28, _⟩ => plane339UnusedGenBound0028
  | ⟨29, _⟩ => plane339UnusedGenBound0029
  | ⟨30, _⟩ => plane339UnusedGenBound0030
  | ⟨k + 31, h⟩ => by omega
theorem plane339UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (0 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (0 : Fin 28) = [296, 98, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0000 (by decide)
theorem plane339UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (1 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (1 : Fin 28) = [296, 98, 16, 6, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0001 (by decide)
theorem plane339UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (2 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (2 : Fin 28) = [290, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0002 (by decide)
theorem plane339UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (3 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (3 : Fin 28) = [292, 98, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0003 (by decide)
theorem plane339UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (4 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (4 : Fin 28) = [294, 98, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0004 (by decide)
theorem plane339UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (5 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (5 : Fin 28) = [264, 66, 32, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0005 (by decide)
theorem plane339UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (6 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (6 : Fin 28) = [268, 70, 36, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0006 (by decide)
theorem plane339UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (7 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (7 : Fin 28) = [270, 68, 38, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0007 (by decide)
theorem plane339UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (8 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (8 : Fin 28) = [258, 72, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0008 (by decide)
theorem plane339UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (9 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (9 : Fin 28) = [262, 76, 46, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0009 (by decide)
theorem plane339UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (10 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (10 : Fin 28) = [296, 128, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0010 (by decide)
theorem plane339UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (11 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (11 : Fin 28) = [296, 130, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0011 (by decide)
theorem plane339UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (12 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (12 : Fin 28) = [296, 132, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0012 (by decide)
theorem plane339UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (13 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (13 : Fin 28) = [296, 136, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0013 (by decide)
theorem plane339UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (14 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (14 : Fin 28) = [296, 138, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0014 (by decide)
theorem plane339UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (15 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (15 : Fin 28) = [296, 140, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0015 (by decide)
theorem plane339UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (16 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (16 : Fin 28) = [296, 142, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0016 (by decide)
theorem plane339UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (17 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (17 : Fin 28) = [296, 160, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0017 (by decide)
theorem plane339UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (18 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (18 : Fin 28) = [296, 164, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0018 (by decide)
theorem plane339UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (19 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (19 : Fin 28) = [296, 166, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0019 (by decide)
theorem plane339UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (20 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (20 : Fin 28) = [296, 168, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0020 (by decide)
theorem plane339UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (21 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (21 : Fin 28) = [296, 170, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0021 (by decide)
theorem plane339UnusedGenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (22 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (22 : Fin 28) = [296, 172, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0022 (by decide)
theorem plane339UnusedGenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (23 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (23 : Fin 28) = [296, 174, 98, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0023 (by decide)
theorem plane339UnusedGenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (24 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (24 : Fin 28) = [264, 66, 32, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0025 (by decide)
theorem plane339UnusedGenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (25 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (25 : Fin 28) = [290, 132, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0027 (by decide)
theorem plane339UnusedGenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (26 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (26 : Fin 28) = [290, 166, 98, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0028 (by decide)
theorem plane339UnusedGenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis (27 : Fin 28))) 15 := by
  rw [show plane339UnusedGenDeadBasis (27 : Fin 28) = [258, 128, 72, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane339UnusedGenSource0029 (by decide)
theorem plane339UnusedGenDeadQRA (d : Fin 28) :
    QuotientRankAtLeast (spanCodes (plane339UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane339UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane339UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane339UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane339UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane339UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane339UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane339UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane339UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane339UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane339UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane339UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane339UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane339UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane339UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane339UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane339UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane339UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane339UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane339UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane339UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane339UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane339UnusedGenDeadBound0021
  | ⟨22, _⟩ => plane339UnusedGenDeadBound0022
  | ⟨23, _⟩ => plane339UnusedGenDeadBound0023
  | ⟨24, _⟩ => plane339UnusedGenDeadBound0024
  | ⟨25, _⟩ => plane339UnusedGenDeadBound0025
  | ⟨26, _⟩ => plane339UnusedGenDeadBound0026
  | ⟨27, _⟩ => plane339UnusedGenDeadBound0027
  | ⟨k + 28, h⟩ => by omega
end QiushiMatmul
