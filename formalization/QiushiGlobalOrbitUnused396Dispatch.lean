import QiushiGlobalOrbitUnused396Bindings00
import QiushiGlobalOrbitUnused396Bindings01
import QiushiGlobalOrbitUnused396Bindings02
import QiushiGlobalOrbitUnused396Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane396UnusedGenSourceQRA (i : Fin 32) :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenSourceBasis i)) (plane396UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane396UnusedGenBound0000
  | ⟨1, _⟩ => plane396UnusedGenBound0001
  | ⟨2, _⟩ => plane396UnusedGenBound0002
  | ⟨3, _⟩ => plane396UnusedGenBound0003
  | ⟨4, _⟩ => plane396UnusedGenBound0004
  | ⟨5, _⟩ => plane396UnusedGenBound0005
  | ⟨6, _⟩ => plane396UnusedGenBound0006
  | ⟨7, _⟩ => plane396UnusedGenBound0007
  | ⟨8, _⟩ => plane396UnusedGenBound0008
  | ⟨9, _⟩ => plane396UnusedGenBound0009
  | ⟨10, _⟩ => plane396UnusedGenBound0010
  | ⟨11, _⟩ => plane396UnusedGenBound0011
  | ⟨12, _⟩ => plane396UnusedGenBound0012
  | ⟨13, _⟩ => plane396UnusedGenBound0013
  | ⟨14, _⟩ => plane396UnusedGenBound0014
  | ⟨15, _⟩ => plane396UnusedGenBound0015
  | ⟨16, _⟩ => plane396UnusedGenBound0016
  | ⟨17, _⟩ => plane396UnusedGenBound0017
  | ⟨18, _⟩ => plane396UnusedGenBound0018
  | ⟨19, _⟩ => plane396UnusedGenBound0019
  | ⟨20, _⟩ => plane396UnusedGenBound0020
  | ⟨21, _⟩ => plane396UnusedGenBound0021
  | ⟨22, _⟩ => plane396UnusedGenBound0022
  | ⟨23, _⟩ => plane396UnusedGenBound0023
  | ⟨24, _⟩ => plane396UnusedGenBound0024
  | ⟨25, _⟩ => plane396UnusedGenBound0025
  | ⟨26, _⟩ => plane396UnusedGenBound0026
  | ⟨27, _⟩ => plane396UnusedGenBound0027
  | ⟨28, _⟩ => plane396UnusedGenBound0028
  | ⟨29, _⟩ => plane396UnusedGenBound0029
  | ⟨30, _⟩ => plane396UnusedGenBound0030
  | ⟨31, _⟩ => plane396UnusedGenBound0031
  | ⟨k + 32, h⟩ => by omega
theorem plane396UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (0 : Fin 19) = [132, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0000 (by decide)
theorem plane396UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (1 : Fin 19) = [133, 96, 20, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0001 (by decide)
theorem plane396UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (2 : Fin 19) = [129, 96, 16, 10, 4] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0002 (by decide)
theorem plane396UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (3 : Fin 19) = [133, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0003 (by decide)
theorem plane396UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (4 : Fin 19) = [133, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0004 (by decide)
theorem plane396UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (5 : Fin 19) = [256, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0005 (by decide)
theorem plane396UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (6 : Fin 19) = [257, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0006 (by decide)
theorem plane396UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (7 : Fin 19) = [258, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0007 (by decide)
theorem plane396UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (8 : Fin 19) = [261, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0008 (by decide)
theorem plane396UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (9 : Fin 19) = [262, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0009 (by decide)
theorem plane396UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (10 : Fin 19) = [263, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0010 (by decide)
theorem plane396UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (11 : Fin 19) = [289, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0011 (by decide)
theorem plane396UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (12 : Fin 19) = [290, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0012 (by decide)
theorem plane396UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (13 : Fin 19) = [291, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0013 (by decide)
theorem plane396UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (14 : Fin 19) = [292, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0014 (by decide)
theorem plane396UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (15 : Fin 19) = [294, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0015 (by decide)
theorem plane396UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (16 : Fin 19) = [295, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0016 (by decide)
theorem plane396UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (17 : Fin 19) = [262, 133, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0020 (by decide)
theorem plane396UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane396UnusedGenDeadBasis (18 : Fin 19) = [257, 133, 71, 39, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane396UnusedGenSource0021 (by decide)
theorem plane396UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane396UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane396UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane396UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane396UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane396UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane396UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane396UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane396UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane396UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane396UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane396UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane396UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane396UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane396UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane396UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane396UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane396UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane396UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane396UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane396UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
