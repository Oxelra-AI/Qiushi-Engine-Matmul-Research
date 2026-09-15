import QiushiPlane275GenBindings00
import QiushiPlane275GenBindings01
import QiushiPlane275GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane275GenSourceQRA (i : Fin 29) :
    QuotientRankAtLeast (spanCodes (plane275GenSourceBasis i)) (plane275GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane275GenBound0000
  | ⟨1, _⟩ => plane275GenBound0001
  | ⟨2, _⟩ => plane275GenBound0002
  | ⟨3, _⟩ => plane275GenBound0003
  | ⟨4, _⟩ => plane275GenBound0004
  | ⟨5, _⟩ => plane275GenBound0005
  | ⟨6, _⟩ => plane275GenBound0006
  | ⟨7, _⟩ => plane275GenBound0007
  | ⟨8, _⟩ => plane275GenBound0008
  | ⟨9, _⟩ => plane275GenBound0009
  | ⟨10, _⟩ => plane275GenBound0010
  | ⟨11, _⟩ => plane275GenBound0011
  | ⟨12, _⟩ => plane275GenBound0012
  | ⟨13, _⟩ => plane275GenBound0013
  | ⟨14, _⟩ => plane275GenBound0014
  | ⟨15, _⟩ => plane275GenBound0015
  | ⟨16, _⟩ => plane275GenBound0016
  | ⟨17, _⟩ => plane275GenBound0017
  | ⟨18, _⟩ => plane275GenBound0018
  | ⟨19, _⟩ => plane275GenBound0019
  | ⟨20, _⟩ => plane275GenBound0020
  | ⟨21, _⟩ => plane275GenBound0021
  | ⟨22, _⟩ => plane275GenBound0022
  | ⟨23, _⟩ => plane275GenBound0023
  | ⟨24, _⟩ => plane275GenBound0024
  | ⟨25, _⟩ => plane275GenBound0025
  | ⟨26, _⟩ => plane275GenBound0026
  | ⟨27, _⟩ => plane275GenBound0027
  | ⟨28, _⟩ => plane275GenBound0028
  | ⟨k + 29, h⟩ => by omega
theorem plane275GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (0 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (0 : Fin 22) = [160, 84, 8, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0000 (by decide)
theorem plane275GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (1 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (1 : Fin 22) = [160, 84, 12, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0001 (by decide)
theorem plane275GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (2 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (2 : Fin 22) = [160, 68, 16, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0002 (by decide)
theorem plane275GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (3 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (3 : Fin 22) = [160, 64, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0003 (by decide)
theorem plane275GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (4 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (4 : Fin 22) = [160, 76, 24, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0004 (by decide)
theorem plane275GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (5 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (5 : Fin 22) = [160, 72, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0005 (by decide)
theorem plane275GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (6 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (6 : Fin 22) = [132, 84, 36, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0006 (by decide)
theorem plane275GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (7 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (7 : Fin 22) = [136, 84, 40, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0007 (by decide)
theorem plane275GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (8 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (8 : Fin 22) = [152, 84, 56, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0008 (by decide)
theorem plane275GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (9 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (9 : Fin 22) = [156, 84, 60, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0009 (by decide)
theorem plane275GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (10 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (10 : Fin 22) = [256, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0010 (by decide)
theorem plane275GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (11 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (11 : Fin 22) = [260, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0011 (by decide)
theorem plane275GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (12 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (12 : Fin 22) = [264, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0012 (by decide)
theorem plane275GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (13 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (13 : Fin 22) = [268, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0013 (by decide)
theorem plane275GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (14 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (14 : Fin 22) = [280, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0014 (by decide)
theorem plane275GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (15 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (15 : Fin 22) = [284, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0015 (by decide)
theorem plane275GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (16 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (16 : Fin 22) = [296, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0016 (by decide)
theorem plane275GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (17 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (17 : Fin 22) = [300, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0017 (by decide)
theorem plane275GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (18 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (18 : Fin 22) = [304, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0018 (by decide)
theorem plane275GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (19 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (19 : Fin 22) = [308, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0019 (by decide)
theorem plane275GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (20 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (20 : Fin 22) = [312, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0020 (by decide)
theorem plane275GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis (21 : Fin 22))) 15 := by
  rw [show plane275GenDeadBasis (21 : Fin 22) = [316, 160, 84, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane275GenSource0021 (by decide)
theorem plane275GenDeadQRA (d : Fin 22) :
    QuotientRankAtLeast (spanCodes (plane275GenDeadBasis d)) 15 :=
  match d with
  | ⟨0, _⟩ => plane275GenDeadBound0000
  | ⟨1, _⟩ => plane275GenDeadBound0001
  | ⟨2, _⟩ => plane275GenDeadBound0002
  | ⟨3, _⟩ => plane275GenDeadBound0003
  | ⟨4, _⟩ => plane275GenDeadBound0004
  | ⟨5, _⟩ => plane275GenDeadBound0005
  | ⟨6, _⟩ => plane275GenDeadBound0006
  | ⟨7, _⟩ => plane275GenDeadBound0007
  | ⟨8, _⟩ => plane275GenDeadBound0008
  | ⟨9, _⟩ => plane275GenDeadBound0009
  | ⟨10, _⟩ => plane275GenDeadBound0010
  | ⟨11, _⟩ => plane275GenDeadBound0011
  | ⟨12, _⟩ => plane275GenDeadBound0012
  | ⟨13, _⟩ => plane275GenDeadBound0013
  | ⟨14, _⟩ => plane275GenDeadBound0014
  | ⟨15, _⟩ => plane275GenDeadBound0015
  | ⟨16, _⟩ => plane275GenDeadBound0016
  | ⟨17, _⟩ => plane275GenDeadBound0017
  | ⟨18, _⟩ => plane275GenDeadBound0018
  | ⟨19, _⟩ => plane275GenDeadBound0019
  | ⟨20, _⟩ => plane275GenDeadBound0020
  | ⟨21, _⟩ => plane275GenDeadBound0021
  | ⟨k + 22, h⟩ => by omega
end QiushiMatmul
