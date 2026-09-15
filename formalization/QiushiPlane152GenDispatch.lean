import QiushiPlane152GenBindings00
import QiushiPlane152GenBindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane152GenSourceQRA (i : Fin 16) :
    QuotientRankAtLeast (spanCodes (plane152GenSourceBasis i)) (plane152GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane152GenBound0000
  | ⟨1, _⟩ => plane152GenBound0001
  | ⟨2, _⟩ => plane152GenBound0002
  | ⟨3, _⟩ => plane152GenBound0003
  | ⟨4, _⟩ => plane152GenBound0004
  | ⟨5, _⟩ => plane152GenBound0005
  | ⟨6, _⟩ => plane152GenBound0006
  | ⟨7, _⟩ => plane152GenBound0007
  | ⟨8, _⟩ => plane152GenBound0008
  | ⟨9, _⟩ => plane152GenBound0009
  | ⟨10, _⟩ => plane152GenBound0010
  | ⟨11, _⟩ => plane152GenBound0011
  | ⟨12, _⟩ => plane152GenBound0012
  | ⟨13, _⟩ => plane152GenBound0013
  | ⟨14, _⟩ => plane152GenBound0014
  | ⟨15, _⟩ => plane152GenBound0015
  | ⟨k + 16, h⟩ => by omega
theorem plane152GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis (0 : Fin 5))) 15 := by
  rw [show plane152GenDeadBasis (0 : Fin 5) = [164, 96, 16, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane152GenSource0000 (by decide)
theorem plane152GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis (1 : Fin 5))) 15 := by
  rw [show plane152GenDeadBasis (1 : Fin 5) = [256, 164, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane152GenSource0001 (by decide)
theorem plane152GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis (2 : Fin 5))) 15 := by
  rw [show plane152GenDeadBasis (2 : Fin 5) = [262, 164, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane152GenSource0002 (by decide)
theorem plane152GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis (3 : Fin 5))) 15 := by
  rw [show plane152GenDeadBasis (3 : Fin 5) = [290, 164, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane152GenSource0003 (by decide)
theorem plane152GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis (4 : Fin 5))) 15 := by
  rw [show plane152GenDeadBasis (4 : Fin 5) = [294, 164, 96, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane152GenSource0004 (by decide)
theorem plane152GenDeadQRA (d : Fin 5) :
    QuotientRankAtLeast (spanCodes (plane152GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane152GenDeadBound0000
  | ⟨1, _⟩ => plane152GenDeadBound0001
  | ⟨2, _⟩ => plane152GenDeadBound0002
  | ⟨3, _⟩ => plane152GenDeadBound0003
  | ⟨4, _⟩ => plane152GenDeadBound0004
  | ⟨k + 5, h⟩ => by omega
end QiushiMatmul
