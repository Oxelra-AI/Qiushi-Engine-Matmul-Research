import QiushiGlobalOrbitUnused302Bindings00
import QiushiGlobalOrbitUnused302Bindings01
import QiushiGlobalOrbitUnused302Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane302UnusedGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenSourceBasis i)) (plane302UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane302UnusedGenBound0000
  | ⟨1, _⟩ => plane302UnusedGenBound0001
  | ⟨2, _⟩ => plane302UnusedGenBound0002
  | ⟨3, _⟩ => plane302UnusedGenBound0003
  | ⟨4, _⟩ => plane302UnusedGenBound0004
  | ⟨5, _⟩ => plane302UnusedGenBound0005
  | ⟨6, _⟩ => plane302UnusedGenBound0006
  | ⟨7, _⟩ => plane302UnusedGenBound0007
  | ⟨8, _⟩ => plane302UnusedGenBound0008
  | ⟨9, _⟩ => plane302UnusedGenBound0009
  | ⟨10, _⟩ => plane302UnusedGenBound0010
  | ⟨11, _⟩ => plane302UnusedGenBound0011
  | ⟨12, _⟩ => plane302UnusedGenBound0012
  | ⟨13, _⟩ => plane302UnusedGenBound0013
  | ⟨14, _⟩ => plane302UnusedGenBound0014
  | ⟨15, _⟩ => plane302UnusedGenBound0015
  | ⟨16, _⟩ => plane302UnusedGenBound0016
  | ⟨17, _⟩ => plane302UnusedGenBound0017
  | ⟨18, _⟩ => plane302UnusedGenBound0018
  | ⟨19, _⟩ => plane302UnusedGenBound0019
  | ⟨20, _⟩ => plane302UnusedGenBound0020
  | ⟨21, _⟩ => plane302UnusedGenBound0021
  | ⟨22, _⟩ => plane302UnusedGenBound0022
  | ⟨23, _⟩ => plane302UnusedGenBound0023
  | ⟨24, _⟩ => plane302UnusedGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane302UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (0 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (0 : Fin 22) = [292, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0000 (by decide)
theorem plane302UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (1 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (1 : Fin 22) = [294, 68, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0001 (by decide)
theorem plane302UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (2 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (2 : Fin 22) = [272, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0002 (by decide)
theorem plane302UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (3 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (3 : Fin 22) = [274, 68, 34, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0003 (by decide)
theorem plane302UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (4 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (4 : Fin 22) = [276, 68, 36, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0004 (by decide)
theorem plane302UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (5 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (5 : Fin 22) = [278, 68, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0005 (by decide)
theorem plane302UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (6 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (6 : Fin 22) = [258, 68, 50, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0006 (by decide)
theorem plane302UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (7 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (7 : Fin 22) = [262, 68, 54, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0007 (by decide)
theorem plane302UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (8 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (8 : Fin 22) = [304, 130, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0008 (by decide)
theorem plane302UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (9 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (9 : Fin 22) = [304, 132, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0009 (by decide)
theorem plane302UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (10 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (10 : Fin 22) = [304, 144, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0010 (by decide)
theorem plane302UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (11 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (11 : Fin 22) = [304, 146, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0011 (by decide)
theorem plane302UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (12 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (12 : Fin 22) = [304, 148, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0012 (by decide)
theorem plane302UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (13 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (13 : Fin 22) = [304, 150, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0013 (by decide)
theorem plane302UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (14 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (14 : Fin 22) = [304, 160, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0014 (by decide)
theorem plane302UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (15 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (15 : Fin 22) = [304, 162, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0015 (by decide)
theorem plane302UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (16 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (16 : Fin 22) = [304, 164, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0016 (by decide)
theorem plane302UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (17 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (17 : Fin 22) = [304, 166, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0017 (by decide)
theorem plane302UnusedGenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (18 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (18 : Fin 22) = [304, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0018 (by decide)
theorem plane302UnusedGenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (19 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (19 : Fin 22) = [304, 178, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0019 (by decide)
theorem plane302UnusedGenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (20 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (20 : Fin 22) = [304, 180, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0020 (by decide)
theorem plane302UnusedGenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis (21 : Fin 22))) 16 := by
  rw [show plane302UnusedGenDeadBasis (21 : Fin 22) = [304, 182, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane302UnusedGenSource0021 (by decide)
theorem plane302UnusedGenDeadQRA (d : Fin 22) :
    QuotientRankAtLeast (spanCodes (plane302UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane302UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane302UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane302UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane302UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane302UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane302UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane302UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane302UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane302UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane302UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane302UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane302UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane302UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane302UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane302UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane302UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane302UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane302UnusedGenDeadBound0017
  | ⟨18, _⟩ => plane302UnusedGenDeadBound0018
  | ⟨19, _⟩ => plane302UnusedGenDeadBound0019
  | ⟨20, _⟩ => plane302UnusedGenDeadBound0020
  | ⟨21, _⟩ => plane302UnusedGenDeadBound0021
  | ⟨k + 22, h⟩ => by omega
end QiushiMatmul
