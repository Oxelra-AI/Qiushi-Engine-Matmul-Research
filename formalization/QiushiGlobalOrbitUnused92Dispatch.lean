import QiushiGlobalOrbitUnused92Bindings00
import QiushiGlobalOrbitUnused92Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane92UnusedGenSourceQRA (i : Fin 11) :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenSourceBasis i)) (plane92UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane92UnusedGenBound0000
  | ⟨1, _⟩ => plane92UnusedGenBound0001
  | ⟨2, _⟩ => plane92UnusedGenBound0002
  | ⟨3, _⟩ => plane92UnusedGenBound0003
  | ⟨4, _⟩ => plane92UnusedGenBound0004
  | ⟨5, _⟩ => plane92UnusedGenBound0005
  | ⟨6, _⟩ => plane92UnusedGenBound0006
  | ⟨7, _⟩ => plane92UnusedGenBound0007
  | ⟨8, _⟩ => plane92UnusedGenBound0008
  | ⟨9, _⟩ => plane92UnusedGenBound0009
  | ⟨10, _⟩ => plane92UnusedGenBound0010
  | ⟨k + 11, h⟩ => by omega
theorem plane92UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (0 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (0 : Fin 6) = [160, 64, 16, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0000 (by decide)
theorem plane92UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (1 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (1 : Fin 6) = [160, 72, 24, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0001 (by decide)
theorem plane92UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (2 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (2 : Fin 6) = [128, 80, 32, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0002 (by decide)
theorem plane92UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (3 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (3 : Fin 6) = [136, 80, 40, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0003 (by decide)
theorem plane92UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (4 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (4 : Fin 6) = [272, 160, 80, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0004 (by decide)
theorem plane92UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis (5 : Fin 6))) 12 := by
  rw [show plane92UnusedGenDeadBasis (5 : Fin 6) = [288, 160, 80, 4, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane92UnusedGenSource0005 (by decide)
theorem plane92UnusedGenDeadQRA (d : Fin 6) :
    QuotientRankAtLeast (spanCodes (plane92UnusedGenDeadBasis d)) 12 :=
  match d with
  | ⟨0, _⟩ => plane92UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane92UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane92UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane92UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane92UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane92UnusedGenDeadBound0005
  | ⟨k + 6, h⟩ => by omega
end QiushiMatmul
