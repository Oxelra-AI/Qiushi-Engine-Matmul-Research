import QiushiGlobalOrbitUnused184Bindings00
import QiushiGlobalOrbitUnused184Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane184UnusedGenSourceQRA (i : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenSourceBasis i)) (plane184UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane184UnusedGenBound0000
  | ⟨1, _⟩ => plane184UnusedGenBound0001
  | ⟨2, _⟩ => plane184UnusedGenBound0002
  | ⟨3, _⟩ => plane184UnusedGenBound0003
  | ⟨4, _⟩ => plane184UnusedGenBound0004
  | ⟨5, _⟩ => plane184UnusedGenBound0005
  | ⟨6, _⟩ => plane184UnusedGenBound0006
  | ⟨7, _⟩ => plane184UnusedGenBound0007
  | ⟨8, _⟩ => plane184UnusedGenBound0008
  | ⟨9, _⟩ => plane184UnusedGenBound0009
  | ⟨10, _⟩ => plane184UnusedGenBound0010
  | ⟨11, _⟩ => plane184UnusedGenBound0011
  | ⟨12, _⟩ => plane184UnusedGenBound0012
  | ⟨13, _⟩ => plane184UnusedGenBound0013
  | ⟨k + 14, h⟩ => by omega
theorem plane184UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (0 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (0 : Fin 13) = [386, 82, 32, 10, 6, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0000 (by decide)
theorem plane184UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (1 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (1 : Fin 13) = [386, 68, 32, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0001 (by decide)
theorem plane184UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (2 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (2 : Fin 13) = [386, 70, 32, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0002 (by decide)
theorem plane184UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (3 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (3 : Fin 13) = [386, 64, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0003 (by decide)
theorem plane184UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (4 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (4 : Fin 13) = [386, 66, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0004 (by decide)
theorem plane184UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (5 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (5 : Fin 13) = [258, 128, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0005 (by decide)
theorem plane184UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (6 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (6 : Fin 13) = [256, 130, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0006 (by decide)
theorem plane184UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (7 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (7 : Fin 13) = [262, 132, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0007 (by decide)
theorem plane184UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (8 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (8 : Fin 13) = [260, 134, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0008 (by decide)
theorem plane184UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (9 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (9 : Fin 13) = [274, 144, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0009 (by decide)
theorem plane184UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (10 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (10 : Fin 13) = [272, 146, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0010 (by decide)
theorem plane184UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (11 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (11 : Fin 13) = [278, 148, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0011 (by decide)
theorem plane184UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis (12 : Fin 13))) 14 := by
  rw [show plane184UnusedGenDeadBasis (12 : Fin 13) = [276, 150, 84, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane184UnusedGenSource0012 (by decide)
theorem plane184UnusedGenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane184UnusedGenDeadBasis d)) 14 :=
  match d with
  | ⟨0, _⟩ => plane184UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane184UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane184UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane184UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane184UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane184UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane184UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane184UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane184UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane184UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane184UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane184UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane184UnusedGenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
