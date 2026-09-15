import QiushiPlane434GenBindings00
import QiushiPlane434GenBindings01
import QiushiPlane434GenBindings02
import QiushiPlane434GenBindings03
import QiushiPlane434GenBindings04
import QiushiPlane434GenBindings05
import QiushiPlane434GenBindings06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane434GenSourceQRA (i : Fin 63) :
    QuotientRankAtLeast (spanCodes (plane434GenSourceBasis i)) (plane434GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane434GenBound0000
  | ⟨1, _⟩ => plane434GenBound0001
  | ⟨2, _⟩ => plane434GenBound0002
  | ⟨3, _⟩ => plane434GenBound0003
  | ⟨4, _⟩ => plane434GenBound0004
  | ⟨5, _⟩ => plane434GenBound0005
  | ⟨6, _⟩ => plane434GenBound0006
  | ⟨7, _⟩ => plane434GenBound0007
  | ⟨8, _⟩ => plane434GenBound0008
  | ⟨9, _⟩ => plane434GenBound0009
  | ⟨10, _⟩ => plane434GenBound0010
  | ⟨11, _⟩ => plane434GenBound0011
  | ⟨12, _⟩ => plane434GenBound0012
  | ⟨13, _⟩ => plane434GenBound0013
  | ⟨14, _⟩ => plane434GenBound0014
  | ⟨15, _⟩ => plane434GenBound0015
  | ⟨16, _⟩ => plane434GenBound0016
  | ⟨17, _⟩ => plane434GenBound0017
  | ⟨18, _⟩ => plane434GenBound0018
  | ⟨19, _⟩ => plane434GenBound0019
  | ⟨20, _⟩ => plane434GenBound0020
  | ⟨21, _⟩ => plane434GenBound0021
  | ⟨22, _⟩ => plane434GenBound0022
  | ⟨23, _⟩ => plane434GenBound0023
  | ⟨24, _⟩ => plane434GenBound0024
  | ⟨25, _⟩ => plane434GenBound0025
  | ⟨26, _⟩ => plane434GenBound0026
  | ⟨27, _⟩ => plane434GenBound0027
  | ⟨28, _⟩ => plane434GenBound0028
  | ⟨29, _⟩ => plane434GenBound0029
  | ⟨30, _⟩ => plane434GenBound0030
  | ⟨31, _⟩ => plane434GenBound0031
  | ⟨32, _⟩ => plane434GenBound0032
  | ⟨33, _⟩ => plane434GenBound0033
  | ⟨34, _⟩ => plane434GenBound0034
  | ⟨35, _⟩ => plane434GenBound0035
  | ⟨36, _⟩ => plane434GenBound0036
  | ⟨37, _⟩ => plane434GenBound0037
  | ⟨38, _⟩ => plane434GenBound0038
  | ⟨39, _⟩ => plane434GenBound0039
  | ⟨40, _⟩ => plane434GenBound0040
  | ⟨41, _⟩ => plane434GenBound0041
  | ⟨42, _⟩ => plane434GenBound0042
  | ⟨43, _⟩ => plane434GenBound0043
  | ⟨44, _⟩ => plane434GenBound0044
  | ⟨45, _⟩ => plane434GenBound0045
  | ⟨46, _⟩ => plane434GenBound0046
  | ⟨47, _⟩ => plane434GenBound0047
  | ⟨48, _⟩ => plane434GenBound0048
  | ⟨49, _⟩ => plane434GenBound0049
  | ⟨50, _⟩ => plane434GenBound0050
  | ⟨51, _⟩ => plane434GenBound0051
  | ⟨52, _⟩ => plane434GenBound0052
  | ⟨53, _⟩ => plane434GenBound0053
  | ⟨54, _⟩ => plane434GenBound0054
  | ⟨55, _⟩ => plane434GenBound0055
  | ⟨56, _⟩ => plane434GenBound0056
  | ⟨57, _⟩ => plane434GenBound0057
  | ⟨58, _⟩ => plane434GenBound0058
  | ⟨59, _⟩ => plane434GenBound0059
  | ⟨60, _⟩ => plane434GenBound0060
  | ⟨61, _⟩ => plane434GenBound0061
  | ⟨62, _⟩ => plane434GenBound0062
  | ⟨k + 63, h⟩ => by omega
theorem plane434GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (0 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (0 : Fin 26) = [256, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0000 (by decide)
theorem plane434GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (1 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (1 : Fin 26) = [262, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0001 (by decide)
theorem plane434GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (2 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (2 : Fin 26) = [266, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0002 (by decide)
theorem plane434GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (3 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (3 : Fin 26) = [266, 66, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0003 (by decide)
theorem plane434GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (4 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (4 : Fin 26) = [266, 70, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0004 (by decide)
theorem plane434GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (5 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (5 : Fin 26) = [266, 76, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0005 (by decide)
theorem plane434GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (6 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (6 : Fin 26) = [266, 66, 34, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0006 (by decide)
theorem plane434GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (7 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (7 : Fin 26) = [266, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0007 (by decide)
theorem plane434GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (8 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (8 : Fin 26) = [266, 108, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0008 (by decide)
theorem plane434GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (9 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (9 : Fin 26) = [266, 110, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0009 (by decide)
theorem plane434GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (10 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (10 : Fin 26) = [266, 136, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0010 (by decide)
theorem plane434GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (11 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (11 : Fin 26) = [262, 132, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0011 (by decide)
theorem plane434GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (12 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (12 : Fin 26) = [266, 162, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0012 (by decide)
theorem plane434GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (13 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (13 : Fin 26) = [266, 164, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0013 (by decide)
theorem plane434GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (14 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (14 : Fin 26) = [266, 166, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0014 (by decide)
theorem plane434GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (15 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (15 : Fin 26) = [266, 168, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0015 (by decide)
theorem plane434GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (16 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (16 : Fin 26) = [266, 174, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0016 (by decide)
theorem plane434GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (17 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (17 : Fin 26) = [266, 196, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0017 (by decide)
theorem plane434GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (18 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (18 : Fin 26) = [266, 198, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0018 (by decide)
theorem plane434GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (19 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (19 : Fin 26) = [266, 206, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0019 (by decide)
theorem plane434GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (20 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (20 : Fin 26) = [266, 224, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0020 (by decide)
theorem plane434GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (21 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (21 : Fin 26) = [266, 230, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0021 (by decide)
theorem plane434GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (22 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (22 : Fin 26) = [266, 232, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0022 (by decide)
theorem plane434GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (23 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (23 : Fin 26) = [266, 234, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0023 (by decide)
theorem plane434GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (24 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (24 : Fin 26) = [266, 236, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0024 (by decide)
theorem plane434GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis (25 : Fin 26))) 16 := by
  rw [show plane434GenDeadBasis (25 : Fin 26) = [266, 238, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane434GenSource0025 (by decide)
theorem plane434GenDeadQRA (d : Fin 26) :
    QuotientRankAtLeast (spanCodes (plane434GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane434GenDeadBound0000
  | ⟨1, _⟩ => plane434GenDeadBound0001
  | ⟨2, _⟩ => plane434GenDeadBound0002
  | ⟨3, _⟩ => plane434GenDeadBound0003
  | ⟨4, _⟩ => plane434GenDeadBound0004
  | ⟨5, _⟩ => plane434GenDeadBound0005
  | ⟨6, _⟩ => plane434GenDeadBound0006
  | ⟨7, _⟩ => plane434GenDeadBound0007
  | ⟨8, _⟩ => plane434GenDeadBound0008
  | ⟨9, _⟩ => plane434GenDeadBound0009
  | ⟨10, _⟩ => plane434GenDeadBound0010
  | ⟨11, _⟩ => plane434GenDeadBound0011
  | ⟨12, _⟩ => plane434GenDeadBound0012
  | ⟨13, _⟩ => plane434GenDeadBound0013
  | ⟨14, _⟩ => plane434GenDeadBound0014
  | ⟨15, _⟩ => plane434GenDeadBound0015
  | ⟨16, _⟩ => plane434GenDeadBound0016
  | ⟨17, _⟩ => plane434GenDeadBound0017
  | ⟨18, _⟩ => plane434GenDeadBound0018
  | ⟨19, _⟩ => plane434GenDeadBound0019
  | ⟨20, _⟩ => plane434GenDeadBound0020
  | ⟨21, _⟩ => plane434GenDeadBound0021
  | ⟨22, _⟩ => plane434GenDeadBound0022
  | ⟨23, _⟩ => plane434GenDeadBound0023
  | ⟨24, _⟩ => plane434GenDeadBound0024
  | ⟨25, _⟩ => plane434GenDeadBound0025
  | ⟨k + 26, h⟩ => by omega
end QiushiMatmul
