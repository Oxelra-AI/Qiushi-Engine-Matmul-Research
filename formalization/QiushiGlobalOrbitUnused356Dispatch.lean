import QiushiGlobalOrbitUnused356Bindings00
import QiushiGlobalOrbitUnused356Bindings01
import QiushiGlobalOrbitUnused356Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane356UnusedGenSourceQRA (i : Fin 27) :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenSourceBasis i)) (plane356UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane356UnusedGenBound0000
  | ⟨1, _⟩ => plane356UnusedGenBound0001
  | ⟨2, _⟩ => plane356UnusedGenBound0002
  | ⟨3, _⟩ => plane356UnusedGenBound0003
  | ⟨4, _⟩ => plane356UnusedGenBound0004
  | ⟨5, _⟩ => plane356UnusedGenBound0005
  | ⟨6, _⟩ => plane356UnusedGenBound0006
  | ⟨7, _⟩ => plane356UnusedGenBound0007
  | ⟨8, _⟩ => plane356UnusedGenBound0008
  | ⟨9, _⟩ => plane356UnusedGenBound0009
  | ⟨10, _⟩ => plane356UnusedGenBound0010
  | ⟨11, _⟩ => plane356UnusedGenBound0011
  | ⟨12, _⟩ => plane356UnusedGenBound0012
  | ⟨13, _⟩ => plane356UnusedGenBound0013
  | ⟨14, _⟩ => plane356UnusedGenBound0014
  | ⟨15, _⟩ => plane356UnusedGenBound0015
  | ⟨16, _⟩ => plane356UnusedGenBound0016
  | ⟨17, _⟩ => plane356UnusedGenBound0017
  | ⟨18, _⟩ => plane356UnusedGenBound0018
  | ⟨19, _⟩ => plane356UnusedGenBound0019
  | ⟨20, _⟩ => plane356UnusedGenBound0020
  | ⟨21, _⟩ => plane356UnusedGenBound0021
  | ⟨22, _⟩ => plane356UnusedGenBound0022
  | ⟨23, _⟩ => plane356UnusedGenBound0023
  | ⟨24, _⟩ => plane356UnusedGenBound0024
  | ⟨25, _⟩ => plane356UnusedGenBound0025
  | ⟨26, _⟩ => plane356UnusedGenBound0026
  | ⟨k + 27, h⟩ => by omega
theorem plane356UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (0 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (0 : Fin 11) = [290, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0001 (by decide)
theorem plane356UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (1 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (1 : Fin 11) = [260, 70, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0002 (by decide)
theorem plane356UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (2 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (2 : Fin 11) = [268, 78, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0003 (by decide)
theorem plane356UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (3 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (3 : Fin 11) = [290, 136, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0004 (by decide)
theorem plane356UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (4 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (4 : Fin 11) = [290, 138, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0005 (by decide)
theorem plane356UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (5 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (5 : Fin 11) = [290, 140, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0006 (by decide)
theorem plane356UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (6 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (6 : Fin 11) = [290, 142, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0007 (by decide)
theorem plane356UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (7 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (7 : Fin 11) = [290, 160, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0008 (by decide)
theorem plane356UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (8 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (8 : Fin 11) = [290, 166, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0010 (by decide)
theorem plane356UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (9 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (9 : Fin 11) = [290, 170, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0011 (by decide)
theorem plane356UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis (10 : Fin 11))) 16 := by
  rw [show plane356UnusedGenDeadBasis (10 : Fin 11) = [290, 172, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane356UnusedGenSource0012 (by decide)
theorem plane356UnusedGenDeadQRA (d : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane356UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane356UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane356UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane356UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane356UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane356UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane356UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane356UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane356UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane356UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane356UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane356UnusedGenDeadBound0010
  | ⟨k + 11, h⟩ => by omega
end QiushiMatmul
