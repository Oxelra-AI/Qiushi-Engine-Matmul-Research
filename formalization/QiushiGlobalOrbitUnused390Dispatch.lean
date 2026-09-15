import QiushiGlobalOrbitUnused390Bindings00
import QiushiGlobalOrbitUnused390Bindings01
import QiushiGlobalOrbitUnused390Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane390UnusedGenSourceQRA (i : Fin 26) :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenSourceBasis i)) (plane390UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane390UnusedGenBound0000
  | ⟨1, _⟩ => plane390UnusedGenBound0001
  | ⟨2, _⟩ => plane390UnusedGenBound0002
  | ⟨3, _⟩ => plane390UnusedGenBound0003
  | ⟨4, _⟩ => plane390UnusedGenBound0004
  | ⟨5, _⟩ => plane390UnusedGenBound0005
  | ⟨6, _⟩ => plane390UnusedGenBound0006
  | ⟨7, _⟩ => plane390UnusedGenBound0007
  | ⟨8, _⟩ => plane390UnusedGenBound0008
  | ⟨9, _⟩ => plane390UnusedGenBound0009
  | ⟨10, _⟩ => plane390UnusedGenBound0010
  | ⟨11, _⟩ => plane390UnusedGenBound0011
  | ⟨12, _⟩ => plane390UnusedGenBound0012
  | ⟨13, _⟩ => plane390UnusedGenBound0013
  | ⟨14, _⟩ => plane390UnusedGenBound0014
  | ⟨15, _⟩ => plane390UnusedGenBound0015
  | ⟨16, _⟩ => plane390UnusedGenBound0016
  | ⟨17, _⟩ => plane390UnusedGenBound0017
  | ⟨18, _⟩ => plane390UnusedGenBound0018
  | ⟨19, _⟩ => plane390UnusedGenBound0019
  | ⟨20, _⟩ => plane390UnusedGenBound0020
  | ⟨21, _⟩ => plane390UnusedGenBound0021
  | ⟨22, _⟩ => plane390UnusedGenBound0022
  | ⟨23, _⟩ => plane390UnusedGenBound0023
  | ⟨24, _⟩ => plane390UnusedGenBound0024
  | ⟨25, _⟩ => plane390UnusedGenBound0025
  | ⟨k + 26, h⟩ => by omega
theorem plane390UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (0 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (0 : Fin 18) = [166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0000 (by decide)
theorem plane390UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (1 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (1 : Fin 18) = [133, 68, 34, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0002 (by decide)
theorem plane390UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (2 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (2 : Fin 18) = [132, 68, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0003 (by decide)
theorem plane390UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (3 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (3 : Fin 18) = [131, 68, 36, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0004 (by decide)
theorem plane390UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (4 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (4 : Fin 18) = [130, 68, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0005 (by decide)
theorem plane390UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (5 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (5 : Fin 18) = [256, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0006 (by decide)
theorem plane390UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (6 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (6 : Fin 18) = [257, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0007 (by decide)
theorem plane390UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (7 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (7 : Fin 18) = [258, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0008 (by decide)
theorem plane390UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (8 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (8 : Fin 18) = [260, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0009 (by decide)
theorem plane390UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (9 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (9 : Fin 18) = [262, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0010 (by decide)
theorem plane390UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (10 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (10 : Fin 18) = [263, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0011 (by decide)
theorem plane390UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (11 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (11 : Fin 18) = [288, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0012 (by decide)
theorem plane390UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (12 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (12 : Fin 18) = [289, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0013 (by decide)
theorem plane390UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (13 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (13 : Fin 18) = [290, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0014 (by decide)
theorem plane390UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (14 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (14 : Fin 18) = [293, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0015 (by decide)
theorem plane390UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (15 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (15 : Fin 18) = [294, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0016 (by decide)
theorem plane390UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (16 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (16 : Fin 18) = [295, 167, 68, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0017 (by decide)
theorem plane390UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis (17 : Fin 18))) 16 := by
  rw [show plane390UnusedGenDeadBasis (17 : Fin 18) = [262, 166, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane390UnusedGenSource0018 (by decide)
theorem plane390UnusedGenDeadQRA (d : Fin 18) :
    QuotientRankAtLeast (spanCodes (plane390UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane390UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane390UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane390UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane390UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane390UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane390UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane390UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane390UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane390UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane390UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane390UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane390UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane390UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane390UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane390UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane390UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane390UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane390UnusedGenDeadBound0017
  | ⟨k + 18, h⟩ => by omega
end QiushiMatmul
