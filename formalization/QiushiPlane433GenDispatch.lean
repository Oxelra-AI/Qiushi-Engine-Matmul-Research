import QiushiPlane433GenBindings00
import QiushiPlane433GenBindings01
import QiushiPlane433GenBindings02
import QiushiPlane433GenBindings03
import QiushiPlane433GenBindings04
import QiushiPlane433GenBindings05
import QiushiPlane433GenBindings06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane433GenSourceQRA (i : Fin 63) :
    QuotientRankAtLeast (spanCodes (plane433GenSourceBasis i)) (plane433GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane433GenBound0000
  | ⟨1, _⟩ => plane433GenBound0001
  | ⟨2, _⟩ => plane433GenBound0002
  | ⟨3, _⟩ => plane433GenBound0003
  | ⟨4, _⟩ => plane433GenBound0004
  | ⟨5, _⟩ => plane433GenBound0005
  | ⟨6, _⟩ => plane433GenBound0006
  | ⟨7, _⟩ => plane433GenBound0007
  | ⟨8, _⟩ => plane433GenBound0008
  | ⟨9, _⟩ => plane433GenBound0009
  | ⟨10, _⟩ => plane433GenBound0010
  | ⟨11, _⟩ => plane433GenBound0011
  | ⟨12, _⟩ => plane433GenBound0012
  | ⟨13, _⟩ => plane433GenBound0013
  | ⟨14, _⟩ => plane433GenBound0014
  | ⟨15, _⟩ => plane433GenBound0015
  | ⟨16, _⟩ => plane433GenBound0016
  | ⟨17, _⟩ => plane433GenBound0017
  | ⟨18, _⟩ => plane433GenBound0018
  | ⟨19, _⟩ => plane433GenBound0019
  | ⟨20, _⟩ => plane433GenBound0020
  | ⟨21, _⟩ => plane433GenBound0021
  | ⟨22, _⟩ => plane433GenBound0022
  | ⟨23, _⟩ => plane433GenBound0023
  | ⟨24, _⟩ => plane433GenBound0024
  | ⟨25, _⟩ => plane433GenBound0025
  | ⟨26, _⟩ => plane433GenBound0026
  | ⟨27, _⟩ => plane433GenBound0027
  | ⟨28, _⟩ => plane433GenBound0028
  | ⟨29, _⟩ => plane433GenBound0029
  | ⟨30, _⟩ => plane433GenBound0030
  | ⟨31, _⟩ => plane433GenBound0031
  | ⟨32, _⟩ => plane433GenBound0032
  | ⟨33, _⟩ => plane433GenBound0033
  | ⟨34, _⟩ => plane433GenBound0034
  | ⟨35, _⟩ => plane433GenBound0035
  | ⟨36, _⟩ => plane433GenBound0036
  | ⟨37, _⟩ => plane433GenBound0037
  | ⟨38, _⟩ => plane433GenBound0038
  | ⟨39, _⟩ => plane433GenBound0039
  | ⟨40, _⟩ => plane433GenBound0040
  | ⟨41, _⟩ => plane433GenBound0041
  | ⟨42, _⟩ => plane433GenBound0042
  | ⟨43, _⟩ => plane433GenBound0043
  | ⟨44, _⟩ => plane433GenBound0044
  | ⟨45, _⟩ => plane433GenBound0045
  | ⟨46, _⟩ => plane433GenBound0046
  | ⟨47, _⟩ => plane433GenBound0047
  | ⟨48, _⟩ => plane433GenBound0048
  | ⟨49, _⟩ => plane433GenBound0049
  | ⟨50, _⟩ => plane433GenBound0050
  | ⟨51, _⟩ => plane433GenBound0051
  | ⟨52, _⟩ => plane433GenBound0052
  | ⟨53, _⟩ => plane433GenBound0053
  | ⟨54, _⟩ => plane433GenBound0054
  | ⟨55, _⟩ => plane433GenBound0055
  | ⟨56, _⟩ => plane433GenBound0056
  | ⟨57, _⟩ => plane433GenBound0057
  | ⟨58, _⟩ => plane433GenBound0058
  | ⟨59, _⟩ => plane433GenBound0059
  | ⟨60, _⟩ => plane433GenBound0060
  | ⟨61, _⟩ => plane433GenBound0061
  | ⟨62, _⟩ => plane433GenBound0062
  | ⟨k + 63, h⟩ => by omega
theorem plane433GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (0 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (0 : Fin 32) = [258, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0000 (by decide)
theorem plane433GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (1 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (1 : Fin 32) = [258, 16, 4, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0001 (by decide)
theorem plane433GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (2 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (2 : Fin 32) = [258, 16, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0002 (by decide)
theorem plane433GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (3 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (3 : Fin 32) = [258, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0003 (by decide)
theorem plane433GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (4 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (4 : Fin 32) = [258, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0004 (by decide)
theorem plane433GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (5 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (5 : Fin 32) = [258, 36, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0005 (by decide)
theorem plane433GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (6 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (6 : Fin 32) = [258, 68, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0006 (by decide)
theorem plane433GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (7 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (7 : Fin 32) = [258, 74, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0007 (by decide)
theorem plane433GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (8 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (8 : Fin 32) = [258, 76, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0008 (by decide)
theorem plane433GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (9 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (9 : Fin 32) = [258, 78, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0009 (by decide)
theorem plane433GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (10 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (10 : Fin 32) = [258, 74, 42, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0010 (by decide)
theorem plane433GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (11 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (11 : Fin 32) = [258, 100, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0011 (by decide)
theorem plane433GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (12 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (12 : Fin 32) = [258, 102, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0012 (by decide)
theorem plane433GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (13 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (13 : Fin 32) = [258, 128, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0013 (by decide)
theorem plane433GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (14 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (14 : Fin 32) = [258, 136, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0014 (by decide)
theorem plane433GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (15 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (15 : Fin 32) = [258, 134, 16, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0015 (by decide)
theorem plane433GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (16 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (16 : Fin 32) = [258, 138, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0016 (by decide)
theorem plane433GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (17 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (17 : Fin 32) = [258, 160, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0017 (by decide)
theorem plane433GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (18 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (18 : Fin 32) = [258, 166, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0018 (by decide)
theorem plane433GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (19 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (19 : Fin 32) = [258, 168, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0019 (by decide)
theorem plane433GenDeadBound0020 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (20 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (20 : Fin 32) = [258, 170, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0020 (by decide)
theorem plane433GenDeadBound0021 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (21 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (21 : Fin 32) = [258, 172, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0021 (by decide)
theorem plane433GenDeadBound0022 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (22 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (22 : Fin 32) = [258, 174, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0022 (by decide)
theorem plane433GenDeadBound0023 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (23 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (23 : Fin 32) = [258, 138, 74, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0023 (by decide)
theorem plane433GenDeadBound0024 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (24 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (24 : Fin 32) = [258, 198, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0024 (by decide)
theorem plane433GenDeadBound0025 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (25 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (25 : Fin 32) = [258, 204, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0025 (by decide)
theorem plane433GenDeadBound0026 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (26 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (26 : Fin 32) = [258, 206, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0026 (by decide)
theorem plane433GenDeadBound0027 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (27 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (27 : Fin 32) = [258, 224, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0027 (by decide)
theorem plane433GenDeadBound0028 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (28 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (28 : Fin 32) = [258, 226, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0028 (by decide)
theorem plane433GenDeadBound0029 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (29 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (29 : Fin 32) = [258, 228, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0029 (by decide)
theorem plane433GenDeadBound0030 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (30 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (30 : Fin 32) = [258, 230, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0030 (by decide)
theorem plane433GenDeadBound0031 :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis (31 : Fin 32))) 16 := by
  rw [show plane433GenDeadBasis (31 : Fin 32) = [258, 238, 16, 1] from rfl]
  exact quotientRankAtLeast_weaken plane433GenSource0031 (by decide)
theorem plane433GenDeadQRA (d : Fin 32) :
    QuotientRankAtLeast (spanCodes (plane433GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane433GenDeadBound0000
  | ⟨1, _⟩ => plane433GenDeadBound0001
  | ⟨2, _⟩ => plane433GenDeadBound0002
  | ⟨3, _⟩ => plane433GenDeadBound0003
  | ⟨4, _⟩ => plane433GenDeadBound0004
  | ⟨5, _⟩ => plane433GenDeadBound0005
  | ⟨6, _⟩ => plane433GenDeadBound0006
  | ⟨7, _⟩ => plane433GenDeadBound0007
  | ⟨8, _⟩ => plane433GenDeadBound0008
  | ⟨9, _⟩ => plane433GenDeadBound0009
  | ⟨10, _⟩ => plane433GenDeadBound0010
  | ⟨11, _⟩ => plane433GenDeadBound0011
  | ⟨12, _⟩ => plane433GenDeadBound0012
  | ⟨13, _⟩ => plane433GenDeadBound0013
  | ⟨14, _⟩ => plane433GenDeadBound0014
  | ⟨15, _⟩ => plane433GenDeadBound0015
  | ⟨16, _⟩ => plane433GenDeadBound0016
  | ⟨17, _⟩ => plane433GenDeadBound0017
  | ⟨18, _⟩ => plane433GenDeadBound0018
  | ⟨19, _⟩ => plane433GenDeadBound0019
  | ⟨20, _⟩ => plane433GenDeadBound0020
  | ⟨21, _⟩ => plane433GenDeadBound0021
  | ⟨22, _⟩ => plane433GenDeadBound0022
  | ⟨23, _⟩ => plane433GenDeadBound0023
  | ⟨24, _⟩ => plane433GenDeadBound0024
  | ⟨25, _⟩ => plane433GenDeadBound0025
  | ⟨26, _⟩ => plane433GenDeadBound0026
  | ⟨27, _⟩ => plane433GenDeadBound0027
  | ⟨28, _⟩ => plane433GenDeadBound0028
  | ⟨29, _⟩ => plane433GenDeadBound0029
  | ⟨30, _⟩ => plane433GenDeadBound0030
  | ⟨31, _⟩ => plane433GenDeadBound0031
  | ⟨k + 32, h⟩ => by omega
end QiushiMatmul
