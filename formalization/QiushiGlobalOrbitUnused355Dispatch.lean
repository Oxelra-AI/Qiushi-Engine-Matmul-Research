import QiushiGlobalOrbitUnused355Bindings00
import QiushiGlobalOrbitUnused355Bindings01
import QiushiGlobalOrbitUnused355Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane355UnusedGenSourceQRA (i : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenSourceBasis i)) (plane355UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane355UnusedGenBound0000
  | ⟨1, _⟩ => plane355UnusedGenBound0001
  | ⟨2, _⟩ => plane355UnusedGenBound0002
  | ⟨3, _⟩ => plane355UnusedGenBound0003
  | ⟨4, _⟩ => plane355UnusedGenBound0004
  | ⟨5, _⟩ => plane355UnusedGenBound0005
  | ⟨6, _⟩ => plane355UnusedGenBound0006
  | ⟨7, _⟩ => plane355UnusedGenBound0007
  | ⟨8, _⟩ => plane355UnusedGenBound0008
  | ⟨9, _⟩ => plane355UnusedGenBound0009
  | ⟨10, _⟩ => plane355UnusedGenBound0010
  | ⟨11, _⟩ => plane355UnusedGenBound0011
  | ⟨12, _⟩ => plane355UnusedGenBound0012
  | ⟨13, _⟩ => plane355UnusedGenBound0013
  | ⟨14, _⟩ => plane355UnusedGenBound0014
  | ⟨15, _⟩ => plane355UnusedGenBound0015
  | ⟨16, _⟩ => plane355UnusedGenBound0016
  | ⟨17, _⟩ => plane355UnusedGenBound0017
  | ⟨18, _⟩ => plane355UnusedGenBound0018
  | ⟨19, _⟩ => plane355UnusedGenBound0019
  | ⟨20, _⟩ => plane355UnusedGenBound0020
  | ⟨k + 21, h⟩ => by omega
theorem plane355UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (0 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (0 : Fin 9) = [130, 70, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0001 (by decide)
theorem plane355UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (1 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (1 : Fin 9) = [142, 74, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0002 (by decide)
theorem plane355UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (2 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (2 : Fin 9) = [138, 78, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0003 (by decide)
theorem plane355UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (3 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (3 : Fin 9) = [258, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0004 (by decide)
theorem plane355UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (4 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (4 : Fin 9) = [266, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0005 (by decide)
theorem plane355UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (5 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (5 : Fin 9) = [270, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0006 (by decide)
theorem plane355UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (6 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (6 : Fin 9) = [294, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0007 (by decide)
theorem plane355UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (7 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (7 : Fin 9) = [298, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0008 (by decide)
theorem plane355UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis (8 : Fin 9))) 16 := by
  rw [show plane355UnusedGenDeadBasis (8 : Fin 9) = [300, 164, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane355UnusedGenSource0009 (by decide)
theorem plane355UnusedGenDeadQRA (d : Fin 9) :
    QuotientRankAtLeast (spanCodes (plane355UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane355UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane355UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane355UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane355UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane355UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane355UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane355UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane355UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane355UnusedGenDeadBound0008
  | ⟨k + 9, h⟩ => by omega
end QiushiMatmul
