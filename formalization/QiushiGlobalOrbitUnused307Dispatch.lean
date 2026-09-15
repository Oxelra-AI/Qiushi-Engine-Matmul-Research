import QiushiGlobalOrbitUnused307Bindings00
import QiushiGlobalOrbitUnused307Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane307UnusedGenSourceQRA (i : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenSourceBasis i)) (plane307UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane307UnusedGenBound0000
  | ⟨1, _⟩ => plane307UnusedGenBound0001
  | ⟨2, _⟩ => plane307UnusedGenBound0002
  | ⟨3, _⟩ => plane307UnusedGenBound0003
  | ⟨4, _⟩ => plane307UnusedGenBound0004
  | ⟨5, _⟩ => plane307UnusedGenBound0005
  | ⟨6, _⟩ => plane307UnusedGenBound0006
  | ⟨7, _⟩ => plane307UnusedGenBound0007
  | ⟨8, _⟩ => plane307UnusedGenBound0008
  | ⟨9, _⟩ => plane307UnusedGenBound0009
  | ⟨10, _⟩ => plane307UnusedGenBound0010
  | ⟨11, _⟩ => plane307UnusedGenBound0011
  | ⟨12, _⟩ => plane307UnusedGenBound0012
  | ⟨13, _⟩ => plane307UnusedGenBound0013
  | ⟨14, _⟩ => plane307UnusedGenBound0014
  | ⟨15, _⟩ => plane307UnusedGenBound0015
  | ⟨16, _⟩ => plane307UnusedGenBound0016
  | ⟨17, _⟩ => plane307UnusedGenBound0017
  | ⟨18, _⟩ => plane307UnusedGenBound0018
  | ⟨19, _⟩ => plane307UnusedGenBound0019
  | ⟨k + 20, h⟩ => by omega
theorem plane307UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (0 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (0 : Fin 12) = [260, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0001 (by decide)
theorem plane307UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (1 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (1 : Fin 12) = [262, 96, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0002 (by decide)
theorem plane307UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (2 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (2 : Fin 12) = [272, 68, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0003 (by decide)
theorem plane307UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (3 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (3 : Fin 12) = [272, 70, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0004 (by decide)
theorem plane307UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (4 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (4 : Fin 12) = [272, 128, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0005 (by decide)
theorem plane307UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (5 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (5 : Fin 12) = [272, 134, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0006 (by decide)
theorem plane307UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (6 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (6 : Fin 12) = [272, 148, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0007 (by decide)
theorem plane307UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (7 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (7 : Fin 12) = [272, 150, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0008 (by decide)
theorem plane307UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (8 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (8 : Fin 12) = [272, 164, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0009 (by decide)
theorem plane307UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (9 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (9 : Fin 12) = [272, 166, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0010 (by decide)
theorem plane307UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (10 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (10 : Fin 12) = [272, 178, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0011 (by decide)
theorem plane307UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis (11 : Fin 12))) 16 := by
  rw [show plane307UnusedGenDeadBasis (11 : Fin 12) = [272, 180, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane307UnusedGenSource0012 (by decide)
theorem plane307UnusedGenDeadQRA (d : Fin 12) :
    QuotientRankAtLeast (spanCodes (plane307UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane307UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane307UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane307UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane307UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane307UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane307UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane307UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane307UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane307UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane307UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane307UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane307UnusedGenDeadBound0011
  | ⟨k + 12, h⟩ => by omega
end QiushiMatmul
