import QiushiGlobalOrbitUnused353Bindings00
import QiushiGlobalOrbitUnused353Bindings01
import QiushiGlobalOrbitUnused353Bindings02
import QiushiGlobalOrbitUnused353Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane353UnusedGenSourceQRA (i : Fin 39) :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenSourceBasis i)) (plane353UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane353UnusedGenBound0000
  | ⟨1, _⟩ => plane353UnusedGenBound0001
  | ⟨2, _⟩ => plane353UnusedGenBound0002
  | ⟨3, _⟩ => plane353UnusedGenBound0003
  | ⟨4, _⟩ => plane353UnusedGenBound0004
  | ⟨5, _⟩ => plane353UnusedGenBound0005
  | ⟨6, _⟩ => plane353UnusedGenBound0006
  | ⟨7, _⟩ => plane353UnusedGenBound0007
  | ⟨8, _⟩ => plane353UnusedGenBound0008
  | ⟨9, _⟩ => plane353UnusedGenBound0009
  | ⟨10, _⟩ => plane353UnusedGenBound0010
  | ⟨11, _⟩ => plane353UnusedGenBound0011
  | ⟨12, _⟩ => plane353UnusedGenBound0012
  | ⟨13, _⟩ => plane353UnusedGenBound0013
  | ⟨14, _⟩ => plane353UnusedGenBound0014
  | ⟨15, _⟩ => plane353UnusedGenBound0015
  | ⟨16, _⟩ => plane353UnusedGenBound0016
  | ⟨17, _⟩ => plane353UnusedGenBound0017
  | ⟨18, _⟩ => plane353UnusedGenBound0018
  | ⟨19, _⟩ => plane353UnusedGenBound0019
  | ⟨20, _⟩ => plane353UnusedGenBound0020
  | ⟨21, _⟩ => plane353UnusedGenBound0021
  | ⟨22, _⟩ => plane353UnusedGenBound0022
  | ⟨23, _⟩ => plane353UnusedGenBound0023
  | ⟨24, _⟩ => plane353UnusedGenBound0024
  | ⟨25, _⟩ => plane353UnusedGenBound0025
  | ⟨26, _⟩ => plane353UnusedGenBound0026
  | ⟨27, _⟩ => plane353UnusedGenBound0027
  | ⟨28, _⟩ => plane353UnusedGenBound0028
  | ⟨29, _⟩ => plane353UnusedGenBound0029
  | ⟨30, _⟩ => plane353UnusedGenBound0030
  | ⟨31, _⟩ => plane353UnusedGenBound0031
  | ⟨32, _⟩ => plane353UnusedGenBound0032
  | ⟨33, _⟩ => plane353UnusedGenBound0033
  | ⟨34, _⟩ => plane353UnusedGenBound0034
  | ⟨35, _⟩ => plane353UnusedGenBound0035
  | ⟨36, _⟩ => plane353UnusedGenBound0036
  | ⟨37, _⟩ => plane353UnusedGenBound0037
  | ⟨38, _⟩ => plane353UnusedGenBound0038
  | ⟨k + 39, h⟩ => by omega
theorem plane353UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (0 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (0 : Fin 11) = [196, 38, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0003 (by decide)
theorem plane353UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (1 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (1 : Fin 11) = [196, 38, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0004 (by decide)
theorem plane353UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (2 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (2 : Fin 11) = [128, 68, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0005 (by decide)
theorem plane353UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (3 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (3 : Fin 11) = [130, 70, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0006 (by decide)
theorem plane353UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (4 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (4 : Fin 11) = [142, 74, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0007 (by decide)
theorem plane353UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (5 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (5 : Fin 11) = [136, 76, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0008 (by decide)
theorem plane353UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (6 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (6 : Fin 11) = [138, 78, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0009 (by decide)
theorem plane353UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (7 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (7 : Fin 11) = [266, 196, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0011 (by decide)
theorem plane353UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (8 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (8 : Fin 11) = [268, 196, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0012 (by decide)
theorem plane353UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (9 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (9 : Fin 11) = [328, 196, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0013 (by decide)
theorem plane353UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis (10 : Fin 11))) 16 := by
  rw [show plane353UnusedGenDeadBasis (10 : Fin 11) = [332, 196, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane353UnusedGenSource0014 (by decide)
theorem plane353UnusedGenDeadQRA (d : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane353UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane353UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane353UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane353UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane353UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane353UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane353UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane353UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane353UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane353UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane353UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane353UnusedGenDeadBound0010
  | ⟨k + 11, h⟩ => by omega
end QiushiMatmul
