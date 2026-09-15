import QiushiGlobalOrbitUnused371Bindings00
import QiushiGlobalOrbitUnused371Bindings01
import QiushiGlobalOrbitUnused371Bindings02
import QiushiGlobalOrbitUnused371Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane371UnusedGenSourceQRA (i : Fin 38) :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenSourceBasis i)) (plane371UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane371UnusedGenBound0000
  | ⟨1, _⟩ => plane371UnusedGenBound0001
  | ⟨2, _⟩ => plane371UnusedGenBound0002
  | ⟨3, _⟩ => plane371UnusedGenBound0003
  | ⟨4, _⟩ => plane371UnusedGenBound0004
  | ⟨5, _⟩ => plane371UnusedGenBound0005
  | ⟨6, _⟩ => plane371UnusedGenBound0006
  | ⟨7, _⟩ => plane371UnusedGenBound0007
  | ⟨8, _⟩ => plane371UnusedGenBound0008
  | ⟨9, _⟩ => plane371UnusedGenBound0009
  | ⟨10, _⟩ => plane371UnusedGenBound0010
  | ⟨11, _⟩ => plane371UnusedGenBound0011
  | ⟨12, _⟩ => plane371UnusedGenBound0012
  | ⟨13, _⟩ => plane371UnusedGenBound0013
  | ⟨14, _⟩ => plane371UnusedGenBound0014
  | ⟨15, _⟩ => plane371UnusedGenBound0015
  | ⟨16, _⟩ => plane371UnusedGenBound0016
  | ⟨17, _⟩ => plane371UnusedGenBound0017
  | ⟨18, _⟩ => plane371UnusedGenBound0018
  | ⟨19, _⟩ => plane371UnusedGenBound0019
  | ⟨20, _⟩ => plane371UnusedGenBound0020
  | ⟨21, _⟩ => plane371UnusedGenBound0021
  | ⟨22, _⟩ => plane371UnusedGenBound0022
  | ⟨23, _⟩ => plane371UnusedGenBound0023
  | ⟨24, _⟩ => plane371UnusedGenBound0024
  | ⟨25, _⟩ => plane371UnusedGenBound0025
  | ⟨26, _⟩ => plane371UnusedGenBound0026
  | ⟨27, _⟩ => plane371UnusedGenBound0027
  | ⟨28, _⟩ => plane371UnusedGenBound0028
  | ⟨29, _⟩ => plane371UnusedGenBound0029
  | ⟨30, _⟩ => plane371UnusedGenBound0030
  | ⟨31, _⟩ => plane371UnusedGenBound0031
  | ⟨32, _⟩ => plane371UnusedGenBound0032
  | ⟨33, _⟩ => plane371UnusedGenBound0033
  | ⟨34, _⟩ => plane371UnusedGenBound0034
  | ⟨35, _⟩ => plane371UnusedGenBound0035
  | ⟨36, _⟩ => plane371UnusedGenBound0036
  | ⟨37, _⟩ => plane371UnusedGenBound0037
  | ⟨k + 38, h⟩ => by omega
theorem plane371UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (0 : Fin 14) = [290, 224, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0000 (by decide)
theorem plane371UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (1 : Fin 14) = [290, 224, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0001 (by decide)
theorem plane371UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (2 : Fin 14) = [290, 224, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0002 (by decide)
theorem plane371UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (3 : Fin 14) = [290, 162, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0005 (by decide)
theorem plane371UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (4 : Fin 14) = [290, 164, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0006 (by decide)
theorem plane371UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (5 : Fin 14) = [290, 166, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0007 (by decide)
theorem plane371UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (6 : Fin 14) = [290, 170, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0008 (by decide)
theorem plane371UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (7 : Fin 14) = [290, 172, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0009 (by decide)
theorem plane371UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (8 : Fin 14) = [290, 174, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0010 (by decide)
theorem plane371UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (9 : Fin 14) = [290, 136, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0012 (by decide)
theorem plane371UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (10 : Fin 14) = [290, 138, 106, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0013 (by decide)
theorem plane371UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (11 : Fin 14) = [290, 140, 108, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0014 (by decide)
theorem plane371UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (12 : Fin 14) = [290, 142, 110, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0015 (by decide)
theorem plane371UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane371UnusedGenDeadBasis (13 : Fin 14) = [290, 166, 70, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane371UnusedGenSource0019 (by decide)
theorem plane371UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane371UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane371UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane371UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane371UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane371UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane371UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane371UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane371UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane371UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane371UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane371UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane371UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane371UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane371UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane371UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
