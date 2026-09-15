import QiushiPlane315GenBindings00
import QiushiPlane315GenBindings01
import QiushiPlane315GenBindings02
import QiushiPlane315GenBindings03
import QiushiPlane315GenBindings04
import QiushiPlane315GenBindings05
import QiushiPlane315GenBindings06
import QiushiPlane315GenBindings07
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane315GenSourceQRA (i : Fin 74) :
    QuotientRankAtLeast (spanCodes (plane315GenSourceBasis i)) (plane315GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane315GenBound0000
  | ⟨1, _⟩ => plane315GenBound0001
  | ⟨2, _⟩ => plane315GenBound0002
  | ⟨3, _⟩ => plane315GenBound0003
  | ⟨4, _⟩ => plane315GenBound0004
  | ⟨5, _⟩ => plane315GenBound0005
  | ⟨6, _⟩ => plane315GenBound0006
  | ⟨7, _⟩ => plane315GenBound0007
  | ⟨8, _⟩ => plane315GenBound0008
  | ⟨9, _⟩ => plane315GenBound0009
  | ⟨10, _⟩ => plane315GenBound0010
  | ⟨11, _⟩ => plane315GenBound0011
  | ⟨12, _⟩ => plane315GenBound0012
  | ⟨13, _⟩ => plane315GenBound0013
  | ⟨14, _⟩ => plane315GenBound0014
  | ⟨15, _⟩ => plane315GenBound0015
  | ⟨16, _⟩ => plane315GenBound0016
  | ⟨17, _⟩ => plane315GenBound0017
  | ⟨18, _⟩ => plane315GenBound0018
  | ⟨19, _⟩ => plane315GenBound0019
  | ⟨20, _⟩ => plane315GenBound0020
  | ⟨21, _⟩ => plane315GenBound0021
  | ⟨22, _⟩ => plane315GenBound0022
  | ⟨23, _⟩ => plane315GenBound0023
  | ⟨24, _⟩ => plane315GenBound0024
  | ⟨25, _⟩ => plane315GenBound0025
  | ⟨26, _⟩ => plane315GenBound0026
  | ⟨27, _⟩ => plane315GenBound0027
  | ⟨28, _⟩ => plane315GenBound0028
  | ⟨29, _⟩ => plane315GenBound0029
  | ⟨30, _⟩ => plane315GenBound0030
  | ⟨31, _⟩ => plane315GenBound0031
  | ⟨32, _⟩ => plane315GenBound0032
  | ⟨33, _⟩ => plane315GenBound0033
  | ⟨34, _⟩ => plane315GenBound0034
  | ⟨35, _⟩ => plane315GenBound0035
  | ⟨36, _⟩ => plane315GenBound0036
  | ⟨37, _⟩ => plane315GenBound0037
  | ⟨38, _⟩ => plane315GenBound0038
  | ⟨39, _⟩ => plane315GenBound0039
  | ⟨40, _⟩ => plane315GenBound0040
  | ⟨41, _⟩ => plane315GenBound0041
  | ⟨42, _⟩ => plane315GenBound0042
  | ⟨43, _⟩ => plane315GenBound0043
  | ⟨44, _⟩ => plane315GenBound0044
  | ⟨45, _⟩ => plane315GenBound0045
  | ⟨46, _⟩ => plane315GenBound0046
  | ⟨47, _⟩ => plane315GenBound0047
  | ⟨48, _⟩ => plane315GenBound0048
  | ⟨49, _⟩ => plane315GenBound0049
  | ⟨50, _⟩ => plane315GenBound0050
  | ⟨51, _⟩ => plane315GenBound0051
  | ⟨52, _⟩ => plane315GenBound0052
  | ⟨53, _⟩ => plane315GenBound0053
  | ⟨54, _⟩ => plane315GenBound0054
  | ⟨55, _⟩ => plane315GenBound0055
  | ⟨56, _⟩ => plane315GenBound0056
  | ⟨57, _⟩ => plane315GenBound0057
  | ⟨58, _⟩ => plane315GenBound0058
  | ⟨59, _⟩ => plane315GenBound0059
  | ⟨60, _⟩ => plane315GenBound0060
  | ⟨61, _⟩ => plane315GenBound0061
  | ⟨62, _⟩ => plane315GenBound0062
  | ⟨63, _⟩ => plane315GenBound0063
  | ⟨64, _⟩ => plane315GenBound0064
  | ⟨65, _⟩ => plane315GenBound0065
  | ⟨66, _⟩ => plane315GenBound0066
  | ⟨67, _⟩ => plane315GenBound0067
  | ⟨68, _⟩ => plane315GenBound0068
  | ⟨69, _⟩ => plane315GenBound0069
  | ⟨70, _⟩ => plane315GenBound0070
  | ⟨71, _⟩ => plane315GenBound0071
  | ⟨72, _⟩ => plane315GenBound0072
  | ⟨73, _⟩ => plane315GenBound0073
  | ⟨k + 74, h⟩ => by omega
theorem plane315GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane315GenDeadBasis (0 : Fin 3))) 16 := by
  rw [show plane315GenDeadBasis (0 : Fin 3) = [260, 160, 70, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane315GenSource0000 (by decide)
theorem plane315GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane315GenDeadBasis (1 : Fin 3))) 16 := by
  rw [show plane315GenDeadBasis (1 : Fin 3) = [260, 160, 116, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane315GenSource0001 (by decide)
theorem plane315GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane315GenDeadBasis (2 : Fin 3))) 16 := by
  rw [show plane315GenDeadBasis (2 : Fin 3) = [260, 160, 118, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane315GenSource0002 (by decide)
theorem plane315GenDeadQRA (d : Fin 3) :
    QuotientRankAtLeast (spanCodes (plane315GenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane315GenDeadBound0000
  | ⟨1, _⟩ => plane315GenDeadBound0001
  | ⟨2, _⟩ => plane315GenDeadBound0002
  | ⟨k + 3, h⟩ => by omega
end QiushiMatmul
