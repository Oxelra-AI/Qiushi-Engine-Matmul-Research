import QiushiGlobalOrbitUnused240Bindings00
import QiushiGlobalOrbitUnused240Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane240UnusedGenSourceQRA (i : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenSourceBasis i)) (plane240UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane240UnusedGenBound0000
  | ⟨1, _⟩ => plane240UnusedGenBound0001
  | ⟨2, _⟩ => plane240UnusedGenBound0002
  | ⟨3, _⟩ => plane240UnusedGenBound0003
  | ⟨4, _⟩ => plane240UnusedGenBound0004
  | ⟨5, _⟩ => plane240UnusedGenBound0005
  | ⟨6, _⟩ => plane240UnusedGenBound0006
  | ⟨7, _⟩ => plane240UnusedGenBound0007
  | ⟨8, _⟩ => plane240UnusedGenBound0008
  | ⟨9, _⟩ => plane240UnusedGenBound0009
  | ⟨10, _⟩ => plane240UnusedGenBound0010
  | ⟨11, _⟩ => plane240UnusedGenBound0011
  | ⟨12, _⟩ => plane240UnusedGenBound0012
  | ⟨13, _⟩ => plane240UnusedGenBound0013
  | ⟨14, _⟩ => plane240UnusedGenBound0014
  | ⟨k + 15, h⟩ => by omega
theorem plane240UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (0 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (0 : Fin 6) = [261, 161, 68, 17, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0001 (by decide)
theorem plane240UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (1 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (1 : Fin 6) = [261, 161, 68, 16, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0002 (by decide)
theorem plane240UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (2 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (2 : Fin 6) = [257, 161, 64, 19, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0003 (by decide)
theorem plane240UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (3 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (3 : Fin 6) = [256, 161, 65, 19, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0004 (by decide)
theorem plane240UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (4 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (4 : Fin 6) = [259, 161, 66, 19, 10, 6] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0005 (by decide)
theorem plane240UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis (5 : Fin 6))) 15 := by
  rw [show plane240UnusedGenDeadBasis (5 : Fin 6) = [258, 161, 67, 19, 10, 7] from rfl]
  exact quotientRankAtLeast_weaken plane240UnusedGenSource0006 (by decide)
theorem plane240UnusedGenDeadQRA (d : Fin 6) :
    QuotientRankAtLeast (spanCodes (plane240UnusedGenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane240UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane240UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane240UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane240UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane240UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane240UnusedGenDeadBound0005
  | ⟨k + 6, h⟩ => by omega
end QiushiMatmul
