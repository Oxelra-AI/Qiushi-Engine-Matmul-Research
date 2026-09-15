import QiushiGlobalOrbitUnused399Bindings00
import QiushiGlobalOrbitUnused399Bindings01
import QiushiGlobalOrbitUnused399Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane399UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenSourceBasis i)) (plane399UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane399UnusedGenBound0000
  | ⟨1, _⟩ => plane399UnusedGenBound0001
  | ⟨2, _⟩ => plane399UnusedGenBound0002
  | ⟨3, _⟩ => plane399UnusedGenBound0003
  | ⟨4, _⟩ => plane399UnusedGenBound0004
  | ⟨5, _⟩ => plane399UnusedGenBound0005
  | ⟨6, _⟩ => plane399UnusedGenBound0006
  | ⟨7, _⟩ => plane399UnusedGenBound0007
  | ⟨8, _⟩ => plane399UnusedGenBound0008
  | ⟨9, _⟩ => plane399UnusedGenBound0009
  | ⟨10, _⟩ => plane399UnusedGenBound0010
  | ⟨11, _⟩ => plane399UnusedGenBound0011
  | ⟨12, _⟩ => plane399UnusedGenBound0012
  | ⟨13, _⟩ => plane399UnusedGenBound0013
  | ⟨14, _⟩ => plane399UnusedGenBound0014
  | ⟨15, _⟩ => plane399UnusedGenBound0015
  | ⟨16, _⟩ => plane399UnusedGenBound0016
  | ⟨17, _⟩ => plane399UnusedGenBound0017
  | ⟨18, _⟩ => plane399UnusedGenBound0018
  | ⟨19, _⟩ => plane399UnusedGenBound0019
  | ⟨20, _⟩ => plane399UnusedGenBound0020
  | ⟨21, _⟩ => plane399UnusedGenBound0021
  | ⟨22, _⟩ => plane399UnusedGenBound0022
  | ⟨23, _⟩ => plane399UnusedGenBound0023
  | ⟨24, _⟩ => plane399UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane399UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (0 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (0 : Fin 18) = [164, 96, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0000 (by decide)
theorem plane399UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (1 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (1 : Fin 18) = [135, 67, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0001 (by decide)
theorem plane399UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (2 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (2 : Fin 18) = [129, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0002 (by decide)
theorem plane399UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (3 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (3 : Fin 18) = [131, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0003 (by decide)
theorem plane399UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (4 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (4 : Fin 18) = [256, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0004 (by decide)
theorem plane399UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (5 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (5 : Fin 18) = [257, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0005 (by decide)
theorem plane399UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (6 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (6 : Fin 18) = [258, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0006 (by decide)
theorem plane399UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (7 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (7 : Fin 18) = [261, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0007 (by decide)
theorem plane399UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (8 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (8 : Fin 18) = [262, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0008 (by decide)
theorem plane399UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (9 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (9 : Fin 18) = [289, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0009 (by decide)
theorem plane399UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (10 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (10 : Fin 18) = [291, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0010 (by decide)
theorem plane399UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (11 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (11 : Fin 18) = [294, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0011 (by decide)
theorem plane399UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (12 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (12 : Fin 18) = [295, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0012 (by decide)
theorem plane399UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (13 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (13 : Fin 18) = [261, 135, 67, 35, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0018 (by decide)
theorem plane399UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (14 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (14 : Fin 18) = [258, 129, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0020 (by decide)
theorem plane399UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (15 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (15 : Fin 18) = [259, 129, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0021 (by decide)
theorem plane399UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (16 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (16 : Fin 18) = [262, 129, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0022 (by decide)
theorem plane399UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis (17 : Fin 18))) 16 := by
  rw [show plane399UnusedGenDeadBasis (17 : Fin 18) = [257, 131, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane399UnusedGenSource0023 (by decide)
theorem plane399UnusedGenDeadQRA (d : Fin 18) :
    QuotientRankAtLeast (spanCodes (plane399UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane399UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane399UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane399UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane399UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane399UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane399UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane399UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane399UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane399UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane399UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane399UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane399UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane399UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane399UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane399UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane399UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane399UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane399UnusedGenDeadBound0017
  | ⟨k + 18, h⟩ => by omega
end QiushiMatmul
