import QiushiPlane419GenBindings00
import QiushiPlane419GenBindings01
import QiushiPlane419GenBindings02
import QiushiPlane419GenBindings03
import QiushiPlane419GenBindings04
import QiushiPlane419GenBindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane419GenSourceQRA (i : Fin 59) :
    QuotientRankAtLeast (spanCodes (plane419GenSourceBasis i)) (plane419GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane419GenBound0000
  | ⟨1, _⟩ => plane419GenBound0001
  | ⟨2, _⟩ => plane419GenBound0002
  | ⟨3, _⟩ => plane419GenBound0003
  | ⟨4, _⟩ => plane419GenBound0004
  | ⟨5, _⟩ => plane419GenBound0005
  | ⟨6, _⟩ => plane419GenBound0006
  | ⟨7, _⟩ => plane419GenBound0007
  | ⟨8, _⟩ => plane419GenBound0008
  | ⟨9, _⟩ => plane419GenBound0009
  | ⟨10, _⟩ => plane419GenBound0010
  | ⟨11, _⟩ => plane419GenBound0011
  | ⟨12, _⟩ => plane419GenBound0012
  | ⟨13, _⟩ => plane419GenBound0013
  | ⟨14, _⟩ => plane419GenBound0014
  | ⟨15, _⟩ => plane419GenBound0015
  | ⟨16, _⟩ => plane419GenBound0016
  | ⟨17, _⟩ => plane419GenBound0017
  | ⟨18, _⟩ => plane419GenBound0018
  | ⟨19, _⟩ => plane419GenBound0019
  | ⟨20, _⟩ => plane419GenBound0020
  | ⟨21, _⟩ => plane419GenBound0021
  | ⟨22, _⟩ => plane419GenBound0022
  | ⟨23, _⟩ => plane419GenBound0023
  | ⟨24, _⟩ => plane419GenBound0024
  | ⟨25, _⟩ => plane419GenBound0025
  | ⟨26, _⟩ => plane419GenBound0026
  | ⟨27, _⟩ => plane419GenBound0027
  | ⟨28, _⟩ => plane419GenBound0028
  | ⟨29, _⟩ => plane419GenBound0029
  | ⟨30, _⟩ => plane419GenBound0030
  | ⟨31, _⟩ => plane419GenBound0031
  | ⟨32, _⟩ => plane419GenBound0032
  | ⟨33, _⟩ => plane419GenBound0033
  | ⟨34, _⟩ => plane419GenBound0034
  | ⟨35, _⟩ => plane419GenBound0035
  | ⟨36, _⟩ => plane419GenBound0036
  | ⟨37, _⟩ => plane419GenBound0037
  | ⟨38, _⟩ => plane419GenBound0038
  | ⟨39, _⟩ => plane419GenBound0039
  | ⟨40, _⟩ => plane419GenBound0040
  | ⟨41, _⟩ => plane419GenBound0041
  | ⟨42, _⟩ => plane419GenBound0042
  | ⟨43, _⟩ => plane419GenBound0043
  | ⟨44, _⟩ => plane419GenBound0044
  | ⟨45, _⟩ => plane419GenBound0045
  | ⟨46, _⟩ => plane419GenBound0046
  | ⟨47, _⟩ => plane419GenBound0047
  | ⟨48, _⟩ => plane419GenBound0048
  | ⟨49, _⟩ => plane419GenBound0049
  | ⟨50, _⟩ => plane419GenBound0050
  | ⟨51, _⟩ => plane419GenBound0051
  | ⟨52, _⟩ => plane419GenBound0052
  | ⟨53, _⟩ => plane419GenBound0053
  | ⟨54, _⟩ => plane419GenBound0054
  | ⟨55, _⟩ => plane419GenBound0055
  | ⟨56, _⟩ => plane419GenBound0056
  | ⟨57, _⟩ => plane419GenBound0057
  | ⟨58, _⟩ => plane419GenBound0058
  | ⟨k + 59, h⟩ => by omega
theorem plane419GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (0 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (0 : Fin 38) = [68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0000 (by decide)
theorem plane419GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (1 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (1 : Fin 38) = [70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0001 (by decide)
theorem plane419GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (2 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (2 : Fin 38) = [32, 10, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0002 (by decide)
theorem plane419GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (3 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (3 : Fin 38) = [64, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0003 (by decide)
theorem plane419GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (4 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (4 : Fin 38) = [66, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0004 (by decide)
theorem plane419GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (5 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (5 : Fin 38) = [68, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0005 (by decide)
theorem plane419GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (6 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (6 : Fin 38) = [70, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0006 (by decide)
theorem plane419GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (7 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (7 : Fin 38) = [68, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0007 (by decide)
theorem plane419GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (8 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (8 : Fin 38) = [132, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0008 (by decide)
theorem plane419GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (9 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (9 : Fin 38) = [134, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0009 (by decide)
theorem plane419GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (10 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (10 : Fin 38) = [148, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0010 (by decide)
theorem plane419GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (11 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (11 : Fin 38) = [150, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0011 (by decide)
theorem plane419GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (12 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (12 : Fin 38) = [196, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0012 (by decide)
theorem plane419GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (13 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (13 : Fin 38) = [198, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0013 (by decide)
theorem plane419GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (14 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (14 : Fin 38) = [212, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0014 (by decide)
theorem plane419GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (15 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (15 : Fin 38) = [214, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0015 (by decide)
theorem plane419GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (16 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (16 : Fin 38) = [258, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0016 (by decide)
theorem plane419GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (17 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (17 : Fin 38) = [262, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0017 (by decide)
theorem plane419GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (18 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (18 : Fin 38) = [262, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0018 (by decide)
theorem plane419GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (19 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (19 : Fin 38) = [262, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0019 (by decide)
theorem plane419GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (20 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (20 : Fin 38) = [258, 32, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0020 (by decide)
theorem plane419GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (21 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (21 : Fin 38) = [258, 32, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0021 (by decide)
theorem plane419GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (22 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (22 : Fin 38) = [262, 70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0022 (by decide)
theorem plane419GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (23 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (23 : Fin 38) = [262, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0023 (by decide)
theorem plane419GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (24 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (24 : Fin 38) = [258, 70, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0024 (by decide)
theorem plane419GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (25 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (25 : Fin 38) = [258, 68, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0025 (by decide)
theorem plane419GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (26 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (26 : Fin 38) = [336, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0026 (by decide)
theorem plane419GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (27 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (27 : Fin 38) = [338, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0027 (by decide)
theorem plane419GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (28 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (28 : Fin 38) = [340, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0028 (by decide)
theorem plane419GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (29 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (29 : Fin 38) = [342, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0029 (by decide)
theorem plane419GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (30 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (30 : Fin 38) = [386, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0030 (by decide)
theorem plane419GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (31 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (31 : Fin 38) = [388, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0031 (by decide)
theorem plane419GenDeadBound0032 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (32 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (32 : Fin 38) = [402, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0032 (by decide)
theorem plane419GenDeadBound0033 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (33 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (33 : Fin 38) = [404, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0033 (by decide)
theorem plane419GenDeadBound0034 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (34 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (34 : Fin 38) = [450, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0034 (by decide)
theorem plane419GenDeadBound0035 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (35 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (35 : Fin 38) = [452, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0035 (by decide)
theorem plane419GenDeadBound0036 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (36 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (36 : Fin 38) = [464, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0036 (by decide)
theorem plane419GenDeadBound0037 :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis (37 : Fin 38))) 16 := by
  rw [show plane419GenDeadBasis (37 : Fin 38) = [470, 32, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane419GenSource0037 (by decide)
theorem plane419GenDeadQRA (d : Fin 38) :
    QuotientRankAtLeast (spanCodes (plane419GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane419GenDeadBound0000
  | ⟨1, _⟩ => plane419GenDeadBound0001
  | ⟨2, _⟩ => plane419GenDeadBound0002
  | ⟨3, _⟩ => plane419GenDeadBound0003
  | ⟨4, _⟩ => plane419GenDeadBound0004
  | ⟨5, _⟩ => plane419GenDeadBound0005
  | ⟨6, _⟩ => plane419GenDeadBound0006
  | ⟨7, _⟩ => plane419GenDeadBound0007
  | ⟨8, _⟩ => plane419GenDeadBound0008
  | ⟨9, _⟩ => plane419GenDeadBound0009
  | ⟨10, _⟩ => plane419GenDeadBound0010
  | ⟨11, _⟩ => plane419GenDeadBound0011
  | ⟨12, _⟩ => plane419GenDeadBound0012
  | ⟨13, _⟩ => plane419GenDeadBound0013
  | ⟨14, _⟩ => plane419GenDeadBound0014
  | ⟨15, _⟩ => plane419GenDeadBound0015
  | ⟨16, _⟩ => plane419GenDeadBound0016
  | ⟨17, _⟩ => plane419GenDeadBound0017
  | ⟨18, _⟩ => plane419GenDeadBound0018
  | ⟨19, _⟩ => plane419GenDeadBound0019
  | ⟨20, _⟩ => plane419GenDeadBound0020
  | ⟨21, _⟩ => plane419GenDeadBound0021
  | ⟨22, _⟩ => plane419GenDeadBound0022
  | ⟨23, _⟩ => plane419GenDeadBound0023
  | ⟨24, _⟩ => plane419GenDeadBound0024
  | ⟨25, _⟩ => plane419GenDeadBound0025
  | ⟨26, _⟩ => plane419GenDeadBound0026
  | ⟨27, _⟩ => plane419GenDeadBound0027
  | ⟨28, _⟩ => plane419GenDeadBound0028
  | ⟨29, _⟩ => plane419GenDeadBound0029
  | ⟨30, _⟩ => plane419GenDeadBound0030
  | ⟨31, _⟩ => plane419GenDeadBound0031
  | ⟨32, _⟩ => plane419GenDeadBound0032
  | ⟨33, _⟩ => plane419GenDeadBound0033
  | ⟨34, _⟩ => plane419GenDeadBound0034
  | ⟨35, _⟩ => plane419GenDeadBound0035
  | ⟨36, _⟩ => plane419GenDeadBound0036
  | ⟨37, _⟩ => plane419GenDeadBound0037
  | ⟨k + 38, h⟩ => by omega
end QiushiMatmul
