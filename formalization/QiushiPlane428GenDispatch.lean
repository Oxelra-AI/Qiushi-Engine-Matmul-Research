import QiushiPlane428GenBindings00
import QiushiPlane428GenBindings01
import QiushiPlane428GenBindings02
import QiushiPlane428GenBindings03
import QiushiPlane428GenBindings04
import QiushiPlane428GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane428GenSourceQRA (i : Fin 51) :
    QuotientRankAtLeast (spanCodes (plane428GenSourceBasis i)) (plane428GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane428GenBound0000
  | ⟨1, _⟩ => plane428GenBound0001
  | ⟨2, _⟩ => plane428GenBound0002
  | ⟨3, _⟩ => plane428GenBound0003
  | ⟨4, _⟩ => plane428GenBound0004
  | ⟨5, _⟩ => plane428GenBound0005
  | ⟨6, _⟩ => plane428GenBound0006
  | ⟨7, _⟩ => plane428GenBound0007
  | ⟨8, _⟩ => plane428GenBound0008
  | ⟨9, _⟩ => plane428GenBound0009
  | ⟨10, _⟩ => plane428GenBound0010
  | ⟨11, _⟩ => plane428GenBound0011
  | ⟨12, _⟩ => plane428GenBound0012
  | ⟨13, _⟩ => plane428GenBound0013
  | ⟨14, _⟩ => plane428GenBound0014
  | ⟨15, _⟩ => plane428GenBound0015
  | ⟨16, _⟩ => plane428GenBound0016
  | ⟨17, _⟩ => plane428GenBound0017
  | ⟨18, _⟩ => plane428GenBound0018
  | ⟨19, _⟩ => plane428GenBound0019
  | ⟨20, _⟩ => plane428GenBound0020
  | ⟨21, _⟩ => plane428GenBound0021
  | ⟨22, _⟩ => plane428GenBound0022
  | ⟨23, _⟩ => plane428GenBound0023
  | ⟨24, _⟩ => plane428GenBound0024
  | ⟨25, _⟩ => plane428GenBound0025
  | ⟨26, _⟩ => plane428GenBound0026
  | ⟨27, _⟩ => plane428GenBound0027
  | ⟨28, _⟩ => plane428GenBound0028
  | ⟨29, _⟩ => plane428GenBound0029
  | ⟨30, _⟩ => plane428GenBound0030
  | ⟨31, _⟩ => plane428GenBound0031
  | ⟨32, _⟩ => plane428GenBound0032
  | ⟨33, _⟩ => plane428GenBound0033
  | ⟨34, _⟩ => plane428GenBound0034
  | ⟨35, _⟩ => plane428GenBound0035
  | ⟨36, _⟩ => plane428GenBound0036
  | ⟨37, _⟩ => plane428GenBound0037
  | ⟨38, _⟩ => plane428GenBound0038
  | ⟨39, _⟩ => plane428GenBound0039
  | ⟨40, _⟩ => plane428GenBound0040
  | ⟨41, _⟩ => plane428GenBound0041
  | ⟨42, _⟩ => plane428GenBound0042
  | ⟨43, _⟩ => plane428GenBound0043
  | ⟨44, _⟩ => plane428GenBound0044
  | ⟨45, _⟩ => plane428GenBound0045
  | ⟨46, _⟩ => plane428GenBound0046
  | ⟨47, _⟩ => plane428GenBound0047
  | ⟨48, _⟩ => plane428GenBound0048
  | ⟨49, _⟩ => plane428GenBound0049
  | ⟨50, _⟩ => plane428GenBound0050
  | ⟨k + 51, h⟩ => by omega
theorem plane428GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (0 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (0 : Fin 19) = [96, 16, 8, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0000 (by decide)
theorem plane428GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (1 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (1 : Fin 19) = [66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0001 (by decide)
theorem plane428GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (2 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (2 : Fin 19) = [74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0002 (by decide)
theorem plane428GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (3 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (3 : Fin 19) = [68, 36, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0003 (by decide)
theorem plane428GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (4 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (4 : Fin 19) = [70, 38, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0004 (by decide)
theorem plane428GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (5 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (5 : Fin 19) = [66, 34, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0005 (by decide)
theorem plane428GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (6 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (6 : Fin 19) = [66, 34, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0006 (by decide)
theorem plane428GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (7 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (7 : Fin 19) = [138, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0007 (by decide)
theorem plane428GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (8 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (8 : Fin 19) = [136, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0008 (by decide)
theorem plane428GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (9 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (9 : Fin 19) = [138, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0009 (by decide)
theorem plane428GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (10 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (10 : Fin 19) = [136, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0010 (by decide)
theorem plane428GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (11 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (11 : Fin 19) = [258, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0011 (by decide)
theorem plane428GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (12 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (12 : Fin 19) = [266, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0012 (by decide)
theorem plane428GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (13 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (13 : Fin 19) = [262, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0013 (by decide)
theorem plane428GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (14 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (14 : Fin 19) = [270, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0014 (by decide)
theorem plane428GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (15 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (15 : Fin 19) = [386, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0015 (by decide)
theorem plane428GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (16 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (16 : Fin 19) = [394, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0016 (by decide)
theorem plane428GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (17 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (17 : Fin 19) = [388, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0017 (by decide)
theorem plane428GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis (18 : Fin 19))) 16 := by
  rw [show plane428GenDeadBasis (18 : Fin 19) = [396, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane428GenSource0018 (by decide)
theorem plane428GenDeadQRA (d : Fin 19) :
    QuotientRankAtLeast (spanCodes (plane428GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane428GenDeadBound0000
  | ⟨1, _⟩ => plane428GenDeadBound0001
  | ⟨2, _⟩ => plane428GenDeadBound0002
  | ⟨3, _⟩ => plane428GenDeadBound0003
  | ⟨4, _⟩ => plane428GenDeadBound0004
  | ⟨5, _⟩ => plane428GenDeadBound0005
  | ⟨6, _⟩ => plane428GenDeadBound0006
  | ⟨7, _⟩ => plane428GenDeadBound0007
  | ⟨8, _⟩ => plane428GenDeadBound0008
  | ⟨9, _⟩ => plane428GenDeadBound0009
  | ⟨10, _⟩ => plane428GenDeadBound0010
  | ⟨11, _⟩ => plane428GenDeadBound0011
  | ⟨12, _⟩ => plane428GenDeadBound0012
  | ⟨13, _⟩ => plane428GenDeadBound0013
  | ⟨14, _⟩ => plane428GenDeadBound0014
  | ⟨15, _⟩ => plane428GenDeadBound0015
  | ⟨16, _⟩ => plane428GenDeadBound0016
  | ⟨17, _⟩ => plane428GenDeadBound0017
  | ⟨18, _⟩ => plane428GenDeadBound0018
  | ⟨k + 19, h⟩ => by omega
end QiushiMatmul
