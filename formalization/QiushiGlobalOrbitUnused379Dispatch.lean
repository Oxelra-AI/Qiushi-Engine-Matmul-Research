import QiushiGlobalOrbitUnused379Bindings00
import QiushiGlobalOrbitUnused379Bindings01
import QiushiGlobalOrbitUnused379Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane379UnusedGenSourceQRA (i : Fin 22) :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenSourceBasis i)) (plane379UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane379UnusedGenBound0000
  | ⟨1, _⟩ => plane379UnusedGenBound0001
  | ⟨2, _⟩ => plane379UnusedGenBound0002
  | ⟨3, _⟩ => plane379UnusedGenBound0003
  | ⟨4, _⟩ => plane379UnusedGenBound0004
  | ⟨5, _⟩ => plane379UnusedGenBound0005
  | ⟨6, _⟩ => plane379UnusedGenBound0006
  | ⟨7, _⟩ => plane379UnusedGenBound0007
  | ⟨8, _⟩ => plane379UnusedGenBound0008
  | ⟨9, _⟩ => plane379UnusedGenBound0009
  | ⟨10, _⟩ => plane379UnusedGenBound0010
  | ⟨11, _⟩ => plane379UnusedGenBound0011
  | ⟨12, _⟩ => plane379UnusedGenBound0012
  | ⟨13, _⟩ => plane379UnusedGenBound0013
  | ⟨14, _⟩ => plane379UnusedGenBound0014
  | ⟨15, _⟩ => plane379UnusedGenBound0015
  | ⟨16, _⟩ => plane379UnusedGenBound0016
  | ⟨17, _⟩ => plane379UnusedGenBound0017
  | ⟨18, _⟩ => plane379UnusedGenBound0018
  | ⟨19, _⟩ => plane379UnusedGenBound0019
  | ⟨20, _⟩ => plane379UnusedGenBound0020
  | ⟨21, _⟩ => plane379UnusedGenBound0021
  | ⟨k + 22, h⟩ => by omega
theorem plane379UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (0 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (0 : Fin 15) = [164, 68, 18, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0000 (by decide)
theorem plane379UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (1 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (1 : Fin 15) = [164, 68, 17, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0001 (by decide)
theorem plane379UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (2 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (2 : Fin 15) = [164, 68, 16, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0002 (by decide)
theorem plane379UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (3 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (3 : Fin 15) = [256, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0003 (by decide)
theorem plane379UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (4 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (4 : Fin 15) = [258, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0004 (by decide)
theorem plane379UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (5 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (5 : Fin 15) = [259, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0005 (by decide)
theorem plane379UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (6 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (6 : Fin 15) = [261, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0006 (by decide)
theorem plane379UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (7 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (7 : Fin 15) = [262, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0007 (by decide)
theorem plane379UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (8 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (8 : Fin 15) = [263, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0008 (by decide)
theorem plane379UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (9 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (9 : Fin 15) = [289, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0009 (by decide)
theorem plane379UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (10 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (10 : Fin 15) = [290, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0010 (by decide)
theorem plane379UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (11 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (11 : Fin 15) = [291, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0011 (by decide)
theorem plane379UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (12 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (12 : Fin 15) = [293, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0012 (by decide)
theorem plane379UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (13 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (13 : Fin 15) = [294, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0013 (by decide)
theorem plane379UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis (14 : Fin 15))) 16 := by
  rw [show plane379UnusedGenDeadBasis (14 : Fin 15) = [295, 164, 68, 19, 10] from rfl]
  exact quotientRankAtLeast_weaken plane379UnusedGenSource0014 (by decide)
theorem plane379UnusedGenDeadQRA (d : Fin 15) :
    QuotientRankAtLeast (spanCodes (plane379UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane379UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane379UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane379UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane379UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane379UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane379UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane379UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane379UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane379UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane379UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane379UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane379UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane379UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane379UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane379UnusedGenDeadBound0014
  | ⟨k + 15, h⟩ => by omega
end QiushiMatmul
