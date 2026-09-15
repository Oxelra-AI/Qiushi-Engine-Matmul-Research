import QiushiGlobalOrbitUnused181Bindings00
import QiushiGlobalOrbitUnused181Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane181UnusedGenSourceQRA (i : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenSourceBasis i)) (plane181UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane181UnusedGenBound0000
  | ⟨1, _⟩ => plane181UnusedGenBound0001
  | ⟨2, _⟩ => plane181UnusedGenBound0002
  | ⟨3, _⟩ => plane181UnusedGenBound0003
  | ⟨4, _⟩ => plane181UnusedGenBound0004
  | ⟨5, _⟩ => plane181UnusedGenBound0005
  | ⟨6, _⟩ => plane181UnusedGenBound0006
  | ⟨7, _⟩ => plane181UnusedGenBound0007
  | ⟨8, _⟩ => plane181UnusedGenBound0008
  | ⟨9, _⟩ => plane181UnusedGenBound0009
  | ⟨10, _⟩ => plane181UnusedGenBound0010
  | ⟨11, _⟩ => plane181UnusedGenBound0011
  | ⟨12, _⟩ => plane181UnusedGenBound0012
  | ⟨k + 13, h⟩ => by omega
theorem plane181UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (0 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (0 : Fin 12) = [258, 68, 32, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0000 (by decide)
theorem plane181UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (1 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (1 : Fin 12) = [258, 70, 32, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0001 (by decide)
theorem plane181UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (2 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (2 : Fin 12) = [258, 64, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0002 (by decide)
theorem plane181UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (3 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (3 : Fin 12) = [258, 66, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0003 (by decide)
theorem plane181UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (4 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (4 : Fin 12) = [258, 128, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0004 (by decide)
theorem plane181UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (5 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (5 : Fin 12) = [258, 130, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0005 (by decide)
theorem plane181UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (6 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (6 : Fin 12) = [258, 132, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0006 (by decide)
theorem plane181UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (7 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (7 : Fin 12) = [258, 134, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0007 (by decide)
theorem plane181UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (8 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (8 : Fin 12) = [258, 144, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0008 (by decide)
theorem plane181UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (9 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (9 : Fin 12) = [258, 146, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0009 (by decide)
theorem plane181UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (10 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (10 : Fin 12) = [258, 148, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0010 (by decide)
theorem plane181UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis (11 : Fin 12))) 14 := by
  rw [show plane181UnusedGenDeadBasis (11 : Fin 12) = [258, 150, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane181UnusedGenSource0011 (by decide)
theorem plane181UnusedGenDeadQRA (d : Fin 12) :
    QuotientRankAtLeast (spanCodes (plane181UnusedGenDeadBasis d)) 14 :=
  match d with
  | ⟨0, _⟩ => plane181UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane181UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane181UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane181UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane181UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane181UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane181UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane181UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane181UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane181UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane181UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane181UnusedGenDeadBound0011
  | ⟨k + 12, h⟩ => by omega
end QiushiMatmul
