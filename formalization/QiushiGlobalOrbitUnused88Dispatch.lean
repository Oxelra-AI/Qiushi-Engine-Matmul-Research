import QiushiGlobalOrbitUnused88Bindings00
import QiushiGlobalOrbitUnused88Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane88UnusedGenSourceQRA (i : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenSourceBasis i)) (plane88UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane88UnusedGenBound0000
  | ⟨1, _⟩ => plane88UnusedGenBound0001
  | ⟨2, _⟩ => plane88UnusedGenBound0002
  | ⟨3, _⟩ => plane88UnusedGenBound0003
  | ⟨4, _⟩ => plane88UnusedGenBound0004
  | ⟨5, _⟩ => plane88UnusedGenBound0005
  | ⟨6, _⟩ => plane88UnusedGenBound0006
  | ⟨7, _⟩ => plane88UnusedGenBound0007
  | ⟨8, _⟩ => plane88UnusedGenBound0008
  | ⟨9, _⟩ => plane88UnusedGenBound0009
  | ⟨10, _⟩ => plane88UnusedGenBound0010
  | ⟨11, _⟩ => plane88UnusedGenBound0011
  | ⟨12, _⟩ => plane88UnusedGenBound0012
  | ⟨k + 13, h⟩ => by omega
theorem plane88UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (0 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (0 : Fin 12) = [80, 32, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0000 (by decide)
theorem plane88UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (1 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (1 : Fin 12) = [80, 48, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0001 (by decide)
theorem plane88UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (2 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (2 : Fin 12) = [128, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0002 (by decide)
theorem plane88UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (3 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (3 : Fin 12) = [144, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0003 (by decide)
theorem plane88UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (4 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (4 : Fin 12) = [256, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0004 (by decide)
theorem plane88UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (5 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (5 : Fin 12) = [272, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0005 (by decide)
theorem plane88UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (6 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (6 : Fin 12) = [288, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0006 (by decide)
theorem plane88UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (7 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (7 : Fin 12) = [304, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0007 (by decide)
theorem plane88UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (8 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (8 : Fin 12) = [384, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0008 (by decide)
theorem plane88UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (9 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (9 : Fin 12) = [400, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0009 (by decide)
theorem plane88UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (10 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (10 : Fin 12) = [416, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0010 (by decide)
theorem plane88UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis (11 : Fin 12))) 12 := by
  rw [show plane88UnusedGenDeadBasis (11 : Fin 12) = [432, 80, 8, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane88UnusedGenSource0011 (by decide)
theorem plane88UnusedGenDeadQRA (d : Fin 12) :
    QuotientRankAtLeast (spanCodes (plane88UnusedGenDeadBasis d)) 12 :=
  match d with
  | ⟨0, _⟩ => plane88UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane88UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane88UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane88UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane88UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane88UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane88UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane88UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane88UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane88UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane88UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane88UnusedGenDeadBound0011
  | ⟨k + 12, h⟩ => by omega
end QiushiMatmul
