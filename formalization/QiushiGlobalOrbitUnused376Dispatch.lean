import QiushiGlobalOrbitUnused376Bindings00
import QiushiGlobalOrbitUnused376Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane376UnusedGenSourceQRA (i : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenSourceBasis i)) (plane376UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane376UnusedGenBound0000
  | ⟨1, _⟩ => plane376UnusedGenBound0001
  | ⟨2, _⟩ => plane376UnusedGenBound0002
  | ⟨3, _⟩ => plane376UnusedGenBound0003
  | ⟨4, _⟩ => plane376UnusedGenBound0004
  | ⟨5, _⟩ => plane376UnusedGenBound0005
  | ⟨6, _⟩ => plane376UnusedGenBound0006
  | ⟨7, _⟩ => plane376UnusedGenBound0007
  | ⟨8, _⟩ => plane376UnusedGenBound0008
  | ⟨9, _⟩ => plane376UnusedGenBound0009
  | ⟨10, _⟩ => plane376UnusedGenBound0010
  | ⟨11, _⟩ => plane376UnusedGenBound0011
  | ⟨12, _⟩ => plane376UnusedGenBound0012
  | ⟨13, _⟩ => plane376UnusedGenBound0013
  | ⟨14, _⟩ => plane376UnusedGenBound0014
  | ⟨k + 15, h⟩ => by omega
theorem plane376UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (0 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (0 : Fin 10) = [256, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0000 (by decide)
theorem plane376UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (1 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (1 : Fin 10) = [257, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0001 (by decide)
theorem plane376UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (2 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (2 : Fin 10) = [258, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0002 (by decide)
theorem plane376UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (3 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (3 : Fin 10) = [259, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0003 (by decide)
theorem plane376UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (4 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (4 : Fin 10) = [262, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0004 (by decide)
theorem plane376UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (5 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (5 : Fin 10) = [263, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0005 (by decide)
theorem plane376UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (6 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (6 : Fin 10) = [289, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0006 (by decide)
theorem plane376UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (7 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (7 : Fin 10) = [290, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0007 (by decide)
theorem plane376UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (8 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (8 : Fin 10) = [293, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0008 (by decide)
theorem plane376UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis (9 : Fin 10))) 16 := by
  rw [show plane376UnusedGenDeadBasis (9 : Fin 10) = [295, 160, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane376UnusedGenSource0009 (by decide)
theorem plane376UnusedGenDeadQRA (d : Fin 10) :
    QuotientRankAtLeast (spanCodes (plane376UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane376UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane376UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane376UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane376UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane376UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane376UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane376UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane376UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane376UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane376UnusedGenDeadBound0009
  | ⟨k + 10, h⟩ => by omega
end QiushiMatmul
