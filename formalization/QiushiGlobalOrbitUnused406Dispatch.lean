import QiushiGlobalOrbitUnused406Bindings00
import QiushiGlobalOrbitUnused406Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane406UnusedGenSourceQRA (i : Fin 18) :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenSourceBasis i)) (plane406UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane406UnusedGenBound0000
  | ⟨1, _⟩ => plane406UnusedGenBound0001
  | ⟨2, _⟩ => plane406UnusedGenBound0002
  | ⟨3, _⟩ => plane406UnusedGenBound0003
  | ⟨4, _⟩ => plane406UnusedGenBound0004
  | ⟨5, _⟩ => plane406UnusedGenBound0005
  | ⟨6, _⟩ => plane406UnusedGenBound0006
  | ⟨7, _⟩ => plane406UnusedGenBound0007
  | ⟨8, _⟩ => plane406UnusedGenBound0008
  | ⟨9, _⟩ => plane406UnusedGenBound0009
  | ⟨10, _⟩ => plane406UnusedGenBound0010
  | ⟨11, _⟩ => plane406UnusedGenBound0011
  | ⟨12, _⟩ => plane406UnusedGenBound0012
  | ⟨13, _⟩ => plane406UnusedGenBound0013
  | ⟨14, _⟩ => plane406UnusedGenBound0014
  | ⟨15, _⟩ => plane406UnusedGenBound0015
  | ⟨16, _⟩ => plane406UnusedGenBound0016
  | ⟨17, _⟩ => plane406UnusedGenBound0017
  | ⟨k + 18, h⟩ => by omega
theorem plane406UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (0 : Fin 14) = [276, 178, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0000 (by decide)
theorem plane406UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (1 : Fin 14) = [263, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0001 (by decide)
theorem plane406UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (2 : Fin 14) = [256, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0002 (by decide)
theorem plane406UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (3 : Fin 14) = [257, 166, 68, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0003 (by decide)
theorem plane406UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (4 : Fin 14) = [258, 165, 68, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0004 (by decide)
theorem plane406UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (5 : Fin 14) = [259, 164, 68, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0005 (by decide)
theorem plane406UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (6 : Fin 14) = [276, 147, 68, 32, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0006 (by decide)
theorem plane406UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (7 : Fin 14) = [276, 145, 68, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0007 (by decide)
theorem plane406UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (8 : Fin 14) = [276, 150, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0008 (by decide)
theorem plane406UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (9 : Fin 14) = [276, 149, 68, 38, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0009 (by decide)
theorem plane406UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (10 : Fin 14) = [276, 130, 68, 49, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0010 (by decide)
theorem plane406UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (11 : Fin 14) = [276, 128, 68, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0011 (by decide)
theorem plane406UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (12 : Fin 14) = [276, 134, 68, 53, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0012 (by decide)
theorem plane406UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane406UnusedGenDeadBasis (13 : Fin 14) = [276, 133, 68, 54, 10] from rfl]
  exact quotientRankAtLeast_weaken plane406UnusedGenSource0013 (by decide)
theorem plane406UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane406UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane406UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane406UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane406UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane406UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane406UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane406UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane406UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane406UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane406UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane406UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane406UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane406UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane406UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane406UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
