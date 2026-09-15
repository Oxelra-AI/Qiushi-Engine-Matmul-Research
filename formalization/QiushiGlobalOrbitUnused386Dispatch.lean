import QiushiGlobalOrbitUnused386Bindings00
import QiushiGlobalOrbitUnused386Bindings01
import QiushiGlobalOrbitUnused386Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane386UnusedGenSourceQRA (i : Fin 21) :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenSourceBasis i)) (plane386UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane386UnusedGenBound0000
  | ⟨1, _⟩ => plane386UnusedGenBound0001
  | ⟨2, _⟩ => plane386UnusedGenBound0002
  | ⟨3, _⟩ => plane386UnusedGenBound0003
  | ⟨4, _⟩ => plane386UnusedGenBound0004
  | ⟨5, _⟩ => plane386UnusedGenBound0005
  | ⟨6, _⟩ => plane386UnusedGenBound0006
  | ⟨7, _⟩ => plane386UnusedGenBound0007
  | ⟨8, _⟩ => plane386UnusedGenBound0008
  | ⟨9, _⟩ => plane386UnusedGenBound0009
  | ⟨10, _⟩ => plane386UnusedGenBound0010
  | ⟨11, _⟩ => plane386UnusedGenBound0011
  | ⟨12, _⟩ => plane386UnusedGenBound0012
  | ⟨13, _⟩ => plane386UnusedGenBound0013
  | ⟨14, _⟩ => plane386UnusedGenBound0014
  | ⟨15, _⟩ => plane386UnusedGenBound0015
  | ⟨16, _⟩ => plane386UnusedGenBound0016
  | ⟨17, _⟩ => plane386UnusedGenBound0017
  | ⟨18, _⟩ => plane386UnusedGenBound0018
  | ⟨19, _⟩ => plane386UnusedGenBound0019
  | ⟨20, _⟩ => plane386UnusedGenBound0020
  | ⟨k + 21, h⟩ => by omega
theorem plane386UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (0 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (0 : Fin 13) = [160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0000 (by decide)
theorem plane386UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (1 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (1 : Fin 13) = [258, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0001 (by decide)
theorem plane386UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (2 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (2 : Fin 13) = [262, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0002 (by decide)
theorem plane386UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (3 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (3 : Fin 13) = [263, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0003 (by decide)
theorem plane386UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (4 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (4 : Fin 13) = [288, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0004 (by decide)
theorem plane386UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (5 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (5 : Fin 13) = [289, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0005 (by decide)
theorem plane386UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (6 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (6 : Fin 13) = [290, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0006 (by decide)
theorem plane386UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (7 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (7 : Fin 13) = [291, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0007 (by decide)
theorem plane386UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (8 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (8 : Fin 13) = [292, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0008 (by decide)
theorem plane386UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (9 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (9 : Fin 13) = [293, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0009 (by decide)
theorem plane386UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (10 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (10 : Fin 13) = [294, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0010 (by decide)
theorem plane386UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (11 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (11 : Fin 13) = [295, 161, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0011 (by decide)
theorem plane386UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis (12 : Fin 13))) 16 := by
  rw [show plane386UnusedGenDeadBasis (12 : Fin 13) = [262, 160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane386UnusedGenSource0012 (by decide)
theorem plane386UnusedGenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane386UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane386UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane386UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane386UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane386UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane386UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane386UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane386UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane386UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane386UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane386UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane386UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane386UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane386UnusedGenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
