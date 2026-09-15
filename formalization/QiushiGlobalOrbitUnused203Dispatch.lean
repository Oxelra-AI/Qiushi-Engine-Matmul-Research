import QiushiGlobalOrbitUnused203Bindings00
import QiushiGlobalOrbitUnused203Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane203UnusedGenSourceQRA (i : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenSourceBasis i)) (plane203UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane203UnusedGenBound0000
  | ⟨1, _⟩ => plane203UnusedGenBound0001
  | ⟨2, _⟩ => plane203UnusedGenBound0002
  | ⟨3, _⟩ => plane203UnusedGenBound0003
  | ⟨4, _⟩ => plane203UnusedGenBound0004
  | ⟨5, _⟩ => plane203UnusedGenBound0005
  | ⟨6, _⟩ => plane203UnusedGenBound0006
  | ⟨7, _⟩ => plane203UnusedGenBound0007
  | ⟨8, _⟩ => plane203UnusedGenBound0008
  | ⟨9, _⟩ => plane203UnusedGenBound0009
  | ⟨10, _⟩ => plane203UnusedGenBound0010
  | ⟨11, _⟩ => plane203UnusedGenBound0011
  | ⟨12, _⟩ => plane203UnusedGenBound0012
  | ⟨13, _⟩ => plane203UnusedGenBound0013
  | ⟨14, _⟩ => plane203UnusedGenBound0014
  | ⟨k + 15, h⟩ => by omega
theorem plane203UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (0 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (0 : Fin 11) = [258, 162, 68, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0000 (by decide)
theorem plane203UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (1 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (1 : Fin 11) = [260, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0001 (by decide)
theorem plane203UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (2 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (2 : Fin 11) = [262, 166, 68, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0002 (by decide)
theorem plane203UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (3 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (3 : Fin 11) = [272, 144, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0003 (by decide)
theorem plane203UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (4 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (4 : Fin 11) = [272, 146, 68, 34, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0004 (by decide)
theorem plane203UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (5 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (5 : Fin 11) = [272, 148, 68, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0005 (by decide)
theorem plane203UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (6 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (6 : Fin 11) = [272, 150, 68, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0006 (by decide)
theorem plane203UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (7 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (7 : Fin 11) = [272, 128, 68, 48, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0007 (by decide)
theorem plane203UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (8 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (8 : Fin 11) = [272, 130, 68, 50, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0008 (by decide)
theorem plane203UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (9 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (9 : Fin 11) = [272, 132, 68, 52, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0009 (by decide)
theorem plane203UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis (10 : Fin 11))) 15 := by
  rw [show plane203UnusedGenDeadBasis (10 : Fin 11) = [272, 134, 68, 54, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane203UnusedGenSource0010 (by decide)
theorem plane203UnusedGenDeadQRA (d : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane203UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane203UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane203UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane203UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane203UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane203UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane203UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane203UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane203UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane203UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane203UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane203UnusedGenDeadBound0010
  | ⟨k + 11, h⟩ => by omega
end QiushiMatmul
