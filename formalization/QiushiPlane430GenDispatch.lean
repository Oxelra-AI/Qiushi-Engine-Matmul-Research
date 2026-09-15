import QiushiPlane430GenBindings00
import QiushiPlane430GenBindings01
import QiushiPlane430GenBindings02
import QiushiPlane430GenBindings03
import QiushiPlane430GenBindings04
import QiushiPlane430GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane430GenSourceQRA (i : Fin 57) :
    QuotientRankAtLeast (spanCodes (plane430GenSourceBasis i)) (plane430GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane430GenBound0000
  | ⟨1, _⟩ => plane430GenBound0001
  | ⟨2, _⟩ => plane430GenBound0002
  | ⟨3, _⟩ => plane430GenBound0003
  | ⟨4, _⟩ => plane430GenBound0004
  | ⟨5, _⟩ => plane430GenBound0005
  | ⟨6, _⟩ => plane430GenBound0006
  | ⟨7, _⟩ => plane430GenBound0007
  | ⟨8, _⟩ => plane430GenBound0008
  | ⟨9, _⟩ => plane430GenBound0009
  | ⟨10, _⟩ => plane430GenBound0010
  | ⟨11, _⟩ => plane430GenBound0011
  | ⟨12, _⟩ => plane430GenBound0012
  | ⟨13, _⟩ => plane430GenBound0013
  | ⟨14, _⟩ => plane430GenBound0014
  | ⟨15, _⟩ => plane430GenBound0015
  | ⟨16, _⟩ => plane430GenBound0016
  | ⟨17, _⟩ => plane430GenBound0017
  | ⟨18, _⟩ => plane430GenBound0018
  | ⟨19, _⟩ => plane430GenBound0019
  | ⟨20, _⟩ => plane430GenBound0020
  | ⟨21, _⟩ => plane430GenBound0021
  | ⟨22, _⟩ => plane430GenBound0022
  | ⟨23, _⟩ => plane430GenBound0023
  | ⟨24, _⟩ => plane430GenBound0024
  | ⟨25, _⟩ => plane430GenBound0025
  | ⟨26, _⟩ => plane430GenBound0026
  | ⟨27, _⟩ => plane430GenBound0027
  | ⟨28, _⟩ => plane430GenBound0028
  | ⟨29, _⟩ => plane430GenBound0029
  | ⟨30, _⟩ => plane430GenBound0030
  | ⟨31, _⟩ => plane430GenBound0031
  | ⟨32, _⟩ => plane430GenBound0032
  | ⟨33, _⟩ => plane430GenBound0033
  | ⟨34, _⟩ => plane430GenBound0034
  | ⟨35, _⟩ => plane430GenBound0035
  | ⟨36, _⟩ => plane430GenBound0036
  | ⟨37, _⟩ => plane430GenBound0037
  | ⟨38, _⟩ => plane430GenBound0038
  | ⟨39, _⟩ => plane430GenBound0039
  | ⟨40, _⟩ => plane430GenBound0040
  | ⟨41, _⟩ => plane430GenBound0041
  | ⟨42, _⟩ => plane430GenBound0042
  | ⟨43, _⟩ => plane430GenBound0043
  | ⟨44, _⟩ => plane430GenBound0044
  | ⟨45, _⟩ => plane430GenBound0045
  | ⟨46, _⟩ => plane430GenBound0046
  | ⟨47, _⟩ => plane430GenBound0047
  | ⟨48, _⟩ => plane430GenBound0048
  | ⟨49, _⟩ => plane430GenBound0049
  | ⟨50, _⟩ => plane430GenBound0050
  | ⟨51, _⟩ => plane430GenBound0051
  | ⟨52, _⟩ => plane430GenBound0052
  | ⟨53, _⟩ => plane430GenBound0053
  | ⟨54, _⟩ => plane430GenBound0054
  | ⟨55, _⟩ => plane430GenBound0055
  | ⟨56, _⟩ => plane430GenBound0056
  | ⟨k + 57, h⟩ => by omega
theorem plane430GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (0 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (0 : Fin 24) = [66, 38, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0000 (by decide)
theorem plane430GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (1 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (1 : Fin 24) = [70, 34, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0001 (by decide)
theorem plane430GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (2 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (2 : Fin 24) = [136, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0002 (by decide)
theorem plane430GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (3 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (3 : Fin 24) = [138, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0003 (by decide)
theorem plane430GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (4 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (4 : Fin 24) = [138, 78, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0004 (by decide)
theorem plane430GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (5 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (5 : Fin 24) = [136, 78, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0005 (by decide)
theorem plane430GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (6 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (6 : Fin 24) = [138, 70, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0006 (by decide)
theorem plane430GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (7 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (7 : Fin 24) = [136, 70, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0007 (by decide)
theorem plane430GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (8 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (8 : Fin 24) = [258, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0008 (by decide)
theorem plane430GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (9 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (9 : Fin 24) = [262, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0009 (by decide)
theorem plane430GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (10 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (10 : Fin 24) = [266, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0010 (by decide)
theorem plane430GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (11 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (11 : Fin 24) = [270, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0011 (by decide)
theorem plane430GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (12 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (12 : Fin 24) = [296, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0012 (by decide)
theorem plane430GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (13 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (13 : Fin 24) = [298, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0013 (by decide)
theorem plane430GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (14 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (14 : Fin 24) = [300, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0014 (by decide)
theorem plane430GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (15 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (15 : Fin 24) = [302, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0015 (by decide)
theorem plane430GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (16 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (16 : Fin 24) = [386, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0016 (by decide)
theorem plane430GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (17 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (17 : Fin 24) = [388, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0017 (by decide)
theorem plane430GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (18 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (18 : Fin 24) = [392, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0018 (by decide)
theorem plane430GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (19 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (19 : Fin 24) = [398, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0019 (by decide)
theorem plane430GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (20 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (20 : Fin 24) = [424, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0020 (by decide)
theorem plane430GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (21 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (21 : Fin 24) = [426, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0021 (by decide)
theorem plane430GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (22 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (22 : Fin 24) = [428, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0022 (by decide)
theorem plane430GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis (23 : Fin 24))) 16 := by
  rw [show plane430GenDeadBasis (23 : Fin 24) = [430, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane430GenSource0023 (by decide)
theorem plane430GenDeadQRA (d : Fin 24) :
    QuotientRankAtLeast (spanCodes (plane430GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane430GenDeadBound0000
  | ⟨1, _⟩ => plane430GenDeadBound0001
  | ⟨2, _⟩ => plane430GenDeadBound0002
  | ⟨3, _⟩ => plane430GenDeadBound0003
  | ⟨4, _⟩ => plane430GenDeadBound0004
  | ⟨5, _⟩ => plane430GenDeadBound0005
  | ⟨6, _⟩ => plane430GenDeadBound0006
  | ⟨7, _⟩ => plane430GenDeadBound0007
  | ⟨8, _⟩ => plane430GenDeadBound0008
  | ⟨9, _⟩ => plane430GenDeadBound0009
  | ⟨10, _⟩ => plane430GenDeadBound0010
  | ⟨11, _⟩ => plane430GenDeadBound0011
  | ⟨12, _⟩ => plane430GenDeadBound0012
  | ⟨13, _⟩ => plane430GenDeadBound0013
  | ⟨14, _⟩ => plane430GenDeadBound0014
  | ⟨15, _⟩ => plane430GenDeadBound0015
  | ⟨16, _⟩ => plane430GenDeadBound0016
  | ⟨17, _⟩ => plane430GenDeadBound0017
  | ⟨18, _⟩ => plane430GenDeadBound0018
  | ⟨19, _⟩ => plane430GenDeadBound0019
  | ⟨20, _⟩ => plane430GenDeadBound0020
  | ⟨21, _⟩ => plane430GenDeadBound0021
  | ⟨22, _⟩ => plane430GenDeadBound0022
  | ⟨23, _⟩ => plane430GenDeadBound0023
  | ⟨k + 24, h⟩ => by omega
end QiushiMatmul
