import QiushiGlobalOrbitUnused398Bindings00
import QiushiGlobalOrbitUnused398Bindings01
import QiushiGlobalOrbitUnused398Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane398UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenSourceBasis i)) (plane398UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane398UnusedGenBound0000
  | ⟨1, _⟩ => plane398UnusedGenBound0001
  | ⟨2, _⟩ => plane398UnusedGenBound0002
  | ⟨3, _⟩ => plane398UnusedGenBound0003
  | ⟨4, _⟩ => plane398UnusedGenBound0004
  | ⟨5, _⟩ => plane398UnusedGenBound0005
  | ⟨6, _⟩ => plane398UnusedGenBound0006
  | ⟨7, _⟩ => plane398UnusedGenBound0007
  | ⟨8, _⟩ => plane398UnusedGenBound0008
  | ⟨9, _⟩ => plane398UnusedGenBound0009
  | ⟨10, _⟩ => plane398UnusedGenBound0010
  | ⟨11, _⟩ => plane398UnusedGenBound0011
  | ⟨12, _⟩ => plane398UnusedGenBound0012
  | ⟨13, _⟩ => plane398UnusedGenBound0013
  | ⟨14, _⟩ => plane398UnusedGenBound0014
  | ⟨15, _⟩ => plane398UnusedGenBound0015
  | ⟨16, _⟩ => plane398UnusedGenBound0016
  | ⟨17, _⟩ => plane398UnusedGenBound0017
  | ⟨18, _⟩ => plane398UnusedGenBound0018
  | ⟨19, _⟩ => plane398UnusedGenBound0019
  | ⟨20, _⟩ => plane398UnusedGenBound0020
  | ⟨21, _⟩ => plane398UnusedGenBound0021
  | ⟨22, _⟩ => plane398UnusedGenBound0022
  | ⟨23, _⟩ => plane398UnusedGenBound0023
  | ⟨24, _⟩ => plane398UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane398UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (0 : Fin 14) = [161, 96, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0000 (by decide)
theorem plane398UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (1 : Fin 14) = [132, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0001 (by decide)
theorem plane398UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (2 : Fin 14) = [135, 70, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0002 (by decide)
theorem plane398UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (3 : Fin 14) = [256, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0003 (by decide)
theorem plane398UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (4 : Fin 14) = [259, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0004 (by decide)
theorem plane398UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (5 : Fin 14) = [260, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0005 (by decide)
theorem plane398UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (6 : Fin 14) = [261, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0006 (by decide)
theorem plane398UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (7 : Fin 14) = [262, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0007 (by decide)
theorem plane398UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (8 : Fin 14) = [263, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0008 (by decide)
theorem plane398UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (9 : Fin 14) = [289, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0009 (by decide)
theorem plane398UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (10 : Fin 14) = [290, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0010 (by decide)
theorem plane398UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (11 : Fin 14) = [291, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0011 (by decide)
theorem plane398UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (12 : Fin 14) = [293, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0012 (by decide)
theorem plane398UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane398UnusedGenDeadBasis (13 : Fin 14) = [294, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane398UnusedGenSource0013 (by decide)
theorem plane398UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane398UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane398UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane398UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane398UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane398UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane398UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane398UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane398UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane398UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane398UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane398UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane398UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane398UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane398UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane398UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
