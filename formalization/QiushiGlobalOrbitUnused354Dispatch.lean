import QiushiGlobalOrbitUnused354Bindings00
import QiushiGlobalOrbitUnused354Bindings01
import QiushiGlobalOrbitUnused354Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane354UnusedGenSourceQRA (i : Fin 30) :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenSourceBasis i)) (plane354UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane354UnusedGenBound0000
  | ⟨1, _⟩ => plane354UnusedGenBound0001
  | ⟨2, _⟩ => plane354UnusedGenBound0002
  | ⟨3, _⟩ => plane354UnusedGenBound0003
  | ⟨4, _⟩ => plane354UnusedGenBound0004
  | ⟨5, _⟩ => plane354UnusedGenBound0005
  | ⟨6, _⟩ => plane354UnusedGenBound0006
  | ⟨7, _⟩ => plane354UnusedGenBound0007
  | ⟨8, _⟩ => plane354UnusedGenBound0008
  | ⟨9, _⟩ => plane354UnusedGenBound0009
  | ⟨10, _⟩ => plane354UnusedGenBound0010
  | ⟨11, _⟩ => plane354UnusedGenBound0011
  | ⟨12, _⟩ => plane354UnusedGenBound0012
  | ⟨13, _⟩ => plane354UnusedGenBound0013
  | ⟨14, _⟩ => plane354UnusedGenBound0014
  | ⟨15, _⟩ => plane354UnusedGenBound0015
  | ⟨16, _⟩ => plane354UnusedGenBound0016
  | ⟨17, _⟩ => plane354UnusedGenBound0017
  | ⟨18, _⟩ => plane354UnusedGenBound0018
  | ⟨19, _⟩ => plane354UnusedGenBound0019
  | ⟨20, _⟩ => plane354UnusedGenBound0020
  | ⟨21, _⟩ => plane354UnusedGenBound0021
  | ⟨22, _⟩ => plane354UnusedGenBound0022
  | ⟨23, _⟩ => plane354UnusedGenBound0023
  | ⟨24, _⟩ => plane354UnusedGenBound0024
  | ⟨25, _⟩ => plane354UnusedGenBound0025
  | ⟨26, _⟩ => plane354UnusedGenBound0026
  | ⟨27, _⟩ => plane354UnusedGenBound0027
  | ⟨28, _⟩ => plane354UnusedGenBound0028
  | ⟨29, _⟩ => plane354UnusedGenBound0029
  | ⟨k + 30, h⟩ => by omega
theorem plane354UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (0 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (0 : Fin 11) = [130, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0001 (by decide)
theorem plane354UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (1 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (1 : Fin 11) = [136, 66, 34, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0002 (by decide)
theorem plane354UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (2 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (2 : Fin 11) = [136, 70, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0004 (by decide)
theorem plane354UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (3 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (3 : Fin 11) = [136, 78, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0006 (by decide)
theorem plane354UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (4 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (4 : Fin 11) = [256, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0007 (by decide)
theorem plane354UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (5 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (5 : Fin 11) = [262, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0008 (by decide)
theorem plane354UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (6 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (6 : Fin 11) = [266, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0010 (by decide)
theorem plane354UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (7 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (7 : Fin 11) = [268, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0011 (by decide)
theorem plane354UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (8 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (8 : Fin 11) = [290, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0012 (by decide)
theorem plane354UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (9 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (9 : Fin 11) = [294, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0013 (by decide)
theorem plane354UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis (10 : Fin 11))) 16 := by
  rw [show plane354UnusedGenDeadBasis (10 : Fin 11) = [302, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane354UnusedGenSource0014 (by decide)
theorem plane354UnusedGenDeadQRA (d : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane354UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane354UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane354UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane354UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane354UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane354UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane354UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane354UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane354UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane354UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane354UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane354UnusedGenDeadBound0010
  | ⟨k + 11, h⟩ => by omega
end QiushiMatmul
