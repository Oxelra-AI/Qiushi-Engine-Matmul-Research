import QiushiGlobalOrbitUnused403Bindings00
import QiushiGlobalOrbitUnused403Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane403UnusedGenSourceQRA (i : Fin 16) :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenSourceBasis i)) (plane403UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane403UnusedGenBound0000
  | ⟨1, _⟩ => plane403UnusedGenBound0001
  | ⟨2, _⟩ => plane403UnusedGenBound0002
  | ⟨3, _⟩ => plane403UnusedGenBound0003
  | ⟨4, _⟩ => plane403UnusedGenBound0004
  | ⟨5, _⟩ => plane403UnusedGenBound0005
  | ⟨6, _⟩ => plane403UnusedGenBound0006
  | ⟨7, _⟩ => plane403UnusedGenBound0007
  | ⟨8, _⟩ => plane403UnusedGenBound0008
  | ⟨9, _⟩ => plane403UnusedGenBound0009
  | ⟨10, _⟩ => plane403UnusedGenBound0010
  | ⟨11, _⟩ => plane403UnusedGenBound0011
  | ⟨12, _⟩ => plane403UnusedGenBound0012
  | ⟨13, _⟩ => plane403UnusedGenBound0013
  | ⟨14, _⟩ => plane403UnusedGenBound0014
  | ⟨15, _⟩ => plane403UnusedGenBound0015
  | ⟨k + 16, h⟩ => by omega
theorem plane403UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (0 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (0 : Fin 13) = [304, 160, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0000 (by decide)
theorem plane403UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (1 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (1 : Fin 13) = [292, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0001 (by decide)
theorem plane403UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (2 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (2 : Fin 13) = [293, 161, 68, 21, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0002 (by decide)
theorem plane403UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (3 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (3 : Fin 13) = [294, 161, 68, 22, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0003 (by decide)
theorem plane403UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (4 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (4 : Fin 13) = [295, 161, 68, 23, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0004 (by decide)
theorem plane403UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (5 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (5 : Fin 13) = [274, 131, 68, 34, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0005 (by decide)
theorem plane403UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (6 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (6 : Fin 13) = [275, 130, 68, 35, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0006 (by decide)
theorem plane403UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (7 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (7 : Fin 13) = [276, 133, 68, 36, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0007 (by decide)
theorem plane403UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (8 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (8 : Fin 13) = [277, 132, 68, 37, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0008 (by decide)
theorem plane403UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (9 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (9 : Fin 13) = [258, 147, 68, 50, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0009 (by decide)
theorem plane403UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (10 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (10 : Fin 13) = [259, 146, 68, 51, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0010 (by decide)
theorem plane403UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (11 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (11 : Fin 13) = [262, 151, 68, 54, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0011 (by decide)
theorem plane403UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis (12 : Fin 13))) 16 := by
  rw [show plane403UnusedGenDeadBasis (12 : Fin 13) = [263, 150, 68, 55, 10] from rfl]
  exact quotientRankAtLeast_weaken plane403UnusedGenSource0012 (by decide)
theorem plane403UnusedGenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane403UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane403UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane403UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane403UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane403UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane403UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane403UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane403UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane403UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane403UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane403UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane403UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane403UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane403UnusedGenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
