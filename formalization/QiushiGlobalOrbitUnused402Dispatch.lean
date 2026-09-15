import QiushiGlobalOrbitUnused402Bindings00
import QiushiGlobalOrbitUnused402Bindings01
import QiushiGlobalOrbitUnused402Bindings02
import QiushiGlobalOrbitUnused402Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane402UnusedGenSourceQRA (i : Fin 31) :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenSourceBasis i)) (plane402UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane402UnusedGenBound0000
  | ⟨1, _⟩ => plane402UnusedGenBound0001
  | ⟨2, _⟩ => plane402UnusedGenBound0002
  | ⟨3, _⟩ => plane402UnusedGenBound0003
  | ⟨4, _⟩ => plane402UnusedGenBound0004
  | ⟨5, _⟩ => plane402UnusedGenBound0005
  | ⟨6, _⟩ => plane402UnusedGenBound0006
  | ⟨7, _⟩ => plane402UnusedGenBound0007
  | ⟨8, _⟩ => plane402UnusedGenBound0008
  | ⟨9, _⟩ => plane402UnusedGenBound0009
  | ⟨10, _⟩ => plane402UnusedGenBound0010
  | ⟨11, _⟩ => plane402UnusedGenBound0011
  | ⟨12, _⟩ => plane402UnusedGenBound0012
  | ⟨13, _⟩ => plane402UnusedGenBound0013
  | ⟨14, _⟩ => plane402UnusedGenBound0014
  | ⟨15, _⟩ => plane402UnusedGenBound0015
  | ⟨16, _⟩ => plane402UnusedGenBound0016
  | ⟨17, _⟩ => plane402UnusedGenBound0017
  | ⟨18, _⟩ => plane402UnusedGenBound0018
  | ⟨19, _⟩ => plane402UnusedGenBound0019
  | ⟨20, _⟩ => plane402UnusedGenBound0020
  | ⟨21, _⟩ => plane402UnusedGenBound0021
  | ⟨22, _⟩ => plane402UnusedGenBound0022
  | ⟨23, _⟩ => plane402UnusedGenBound0023
  | ⟨24, _⟩ => plane402UnusedGenBound0024
  | ⟨25, _⟩ => plane402UnusedGenBound0025
  | ⟨26, _⟩ => plane402UnusedGenBound0026
  | ⟨27, _⟩ => plane402UnusedGenBound0027
  | ⟨28, _⟩ => plane402UnusedGenBound0028
  | ⟨29, _⟩ => plane402UnusedGenBound0029
  | ⟨30, _⟩ => plane402UnusedGenBound0030
  | ⟨k + 31, h⟩ => by omega
theorem plane402UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (0 : Fin 19) = [389, 96, 20, 8, 2] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0000 (by decide)
theorem plane402UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (1 : Fin 19) = [388, 96, 20, 9, 3] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0001 (by decide)
theorem plane402UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (2 : Fin 19) = [386, 96, 17, 10, 5] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0002 (by decide)
theorem plane402UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (3 : Fin 19) = [391, 65, 33, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0004 (by decide)
theorem plane402UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (4 : Fin 19) = [391, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0005 (by decide)
theorem plane402UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (5 : Fin 19) = [391, 70, 38, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0006 (by decide)
theorem plane402UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (6 : Fin 19) = [262, 129, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0007 (by decide)
theorem plane402UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (7 : Fin 19) = [261, 130, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0008 (by decide)
theorem plane402UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (8 : Fin 19) = [260, 131, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0009 (by decide)
theorem plane402UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (9 : Fin 19) = [259, 132, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0010 (by decide)
theorem plane402UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (10 : Fin 19) = [258, 133, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0011 (by decide)
theorem plane402UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (11 : Fin 19) = [256, 135, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0012 (by decide)
theorem plane402UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (12 : Fin 19) = [295, 160, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0013 (by decide)
theorem plane402UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (13 : Fin 19) = [294, 161, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0014 (by decide)
theorem plane402UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (14 : Fin 19) = [293, 162, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0015 (by decide)
theorem plane402UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (15 : Fin 19) = [291, 164, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0016 (by decide)
theorem plane402UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (16 : Fin 19) = [289, 166, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0017 (by decide)
theorem plane402UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (17 : Fin 19) = [288, 167, 96, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0018 (by decide)
theorem plane402UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane402UnusedGenDeadBasis (18 : Fin 19) = [262, 129, 69, 37, 20, 10] from rfl]
  exact quotientRankAtLeast_weaken plane402UnusedGenSource0022 (by decide)
theorem plane402UnusedGenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane402UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane402UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane402UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane402UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane402UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane402UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane402UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane402UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane402UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane402UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane402UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane402UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane402UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane402UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane402UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane402UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane402UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane402UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane402UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane402UnusedGenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
