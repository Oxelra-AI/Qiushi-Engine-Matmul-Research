import QiushiFrozenRank361Bindings00
import QiushiFrozenRank361Bindings01
import QiushiFrozenRank361Bindings02
import QiushiFrozenRank361Bindings03
import QiushiFrozenRank361Bindings04
import QiushiFrozenRank361Bindings05
import QiushiFrozenRank361Bindings06
import QiushiFrozenRank361Bindings07
import QiushiFrozenRank361Bindings08
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane361RankCoverGenSourceQRA (i : Fin 86) :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenSourceBasis i)) (plane361RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane361RankCoverGenBound0000
  | ⟨1, _⟩ => plane361RankCoverGenBound0001
  | ⟨2, _⟩ => plane361RankCoverGenBound0002
  | ⟨3, _⟩ => plane361RankCoverGenBound0003
  | ⟨4, _⟩ => plane361RankCoverGenBound0004
  | ⟨5, _⟩ => plane361RankCoverGenBound0005
  | ⟨6, _⟩ => plane361RankCoverGenBound0006
  | ⟨7, _⟩ => plane361RankCoverGenBound0007
  | ⟨8, _⟩ => plane361RankCoverGenBound0008
  | ⟨9, _⟩ => plane361RankCoverGenBound0009
  | ⟨10, _⟩ => plane361RankCoverGenBound0010
  | ⟨11, _⟩ => plane361RankCoverGenBound0011
  | ⟨12, _⟩ => plane361RankCoverGenBound0012
  | ⟨13, _⟩ => plane361RankCoverGenBound0013
  | ⟨14, _⟩ => plane361RankCoverGenBound0014
  | ⟨15, _⟩ => plane361RankCoverGenBound0015
  | ⟨16, _⟩ => plane361RankCoverGenBound0016
  | ⟨17, _⟩ => plane361RankCoverGenBound0017
  | ⟨18, _⟩ => plane361RankCoverGenBound0018
  | ⟨19, _⟩ => plane361RankCoverGenBound0019
  | ⟨20, _⟩ => plane361RankCoverGenBound0020
  | ⟨21, _⟩ => plane361RankCoverGenBound0021
  | ⟨22, _⟩ => plane361RankCoverGenBound0022
  | ⟨23, _⟩ => plane361RankCoverGenBound0023
  | ⟨24, _⟩ => plane361RankCoverGenBound0024
  | ⟨25, _⟩ => plane361RankCoverGenBound0025
  | ⟨26, _⟩ => plane361RankCoverGenBound0026
  | ⟨27, _⟩ => plane361RankCoverGenBound0027
  | ⟨28, _⟩ => plane361RankCoverGenBound0028
  | ⟨29, _⟩ => plane361RankCoverGenBound0029
  | ⟨30, _⟩ => plane361RankCoverGenBound0030
  | ⟨31, _⟩ => plane361RankCoverGenBound0031
  | ⟨32, _⟩ => plane361RankCoverGenBound0032
  | ⟨33, _⟩ => plane361RankCoverGenBound0033
  | ⟨34, _⟩ => plane361RankCoverGenBound0034
  | ⟨35, _⟩ => plane361RankCoverGenBound0035
  | ⟨36, _⟩ => plane361RankCoverGenBound0036
  | ⟨37, _⟩ => plane361RankCoverGenBound0037
  | ⟨38, _⟩ => plane361RankCoverGenBound0038
  | ⟨39, _⟩ => plane361RankCoverGenBound0039
  | ⟨40, _⟩ => plane361RankCoverGenBound0040
  | ⟨41, _⟩ => plane361RankCoverGenBound0041
  | ⟨42, _⟩ => plane361RankCoverGenBound0042
  | ⟨43, _⟩ => plane361RankCoverGenBound0043
  | ⟨44, _⟩ => plane361RankCoverGenBound0044
  | ⟨45, _⟩ => plane361RankCoverGenBound0045
  | ⟨46, _⟩ => plane361RankCoverGenBound0046
  | ⟨47, _⟩ => plane361RankCoverGenBound0047
  | ⟨48, _⟩ => plane361RankCoverGenBound0048
  | ⟨49, _⟩ => plane361RankCoverGenBound0049
  | ⟨50, _⟩ => plane361RankCoverGenBound0050
  | ⟨51, _⟩ => plane361RankCoverGenBound0051
  | ⟨52, _⟩ => plane361RankCoverGenBound0052
  | ⟨53, _⟩ => plane361RankCoverGenBound0053
  | ⟨54, _⟩ => plane361RankCoverGenBound0054
  | ⟨55, _⟩ => plane361RankCoverGenBound0055
  | ⟨56, _⟩ => plane361RankCoverGenBound0056
  | ⟨57, _⟩ => plane361RankCoverGenBound0057
  | ⟨58, _⟩ => plane361RankCoverGenBound0058
  | ⟨59, _⟩ => plane361RankCoverGenBound0059
  | ⟨60, _⟩ => plane361RankCoverGenBound0060
  | ⟨61, _⟩ => plane361RankCoverGenBound0061
  | ⟨62, _⟩ => plane361RankCoverGenBound0062
  | ⟨63, _⟩ => plane361RankCoverGenBound0063
  | ⟨64, _⟩ => plane361RankCoverGenBound0064
  | ⟨65, _⟩ => plane361RankCoverGenBound0065
  | ⟨66, _⟩ => plane361RankCoverGenBound0066
  | ⟨67, _⟩ => plane361RankCoverGenBound0067
  | ⟨68, _⟩ => plane361RankCoverGenBound0068
  | ⟨69, _⟩ => plane361RankCoverGenBound0069
  | ⟨70, _⟩ => plane361RankCoverGenBound0070
  | ⟨71, _⟩ => plane361RankCoverGenBound0071
  | ⟨72, _⟩ => plane361RankCoverGenBound0072
  | ⟨73, _⟩ => plane361RankCoverGenBound0073
  | ⟨74, _⟩ => plane361RankCoverGenBound0074
  | ⟨75, _⟩ => plane361RankCoverGenBound0075
  | ⟨76, _⟩ => plane361RankCoverGenBound0076
  | ⟨77, _⟩ => plane361RankCoverGenBound0077
  | ⟨78, _⟩ => plane361RankCoverGenBound0078
  | ⟨79, _⟩ => plane361RankCoverGenBound0079
  | ⟨80, _⟩ => plane361RankCoverGenBound0080
  | ⟨81, _⟩ => plane361RankCoverGenBound0081
  | ⟨82, _⟩ => plane361RankCoverGenBound0082
  | ⟨83, _⟩ => plane361RankCoverGenBound0083
  | ⟨84, _⟩ => plane361RankCoverGenBound0084
  | ⟨85, _⟩ => plane361RankCoverGenBound0085
  | ⟨k + 86, h⟩ => by omega
theorem plane361RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (0 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (0 : Fin 7) = [294, 100, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0002 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (1 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (1 : Fin 7) = [268, 66, 38, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0003 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (2 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (2 : Fin 7) = [260, 74, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0004 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (3 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (3 : Fin 7) = [298, 138, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0006 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (4 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (4 : Fin 7) = [298, 140, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0007 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (5 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (5 : Fin 7) = [298, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0009 (by decide +kernel)
theorem plane361RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis (6 : Fin 7))) 16 := by
  rw [show plane361RankCoverGenDeadBasis (6 : Fin 7) = [298, 174, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane361RankCoverGenSource0012 (by decide +kernel)
theorem plane361RankCoverGenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane361RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane361RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane361RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane361RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane361RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane361RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane361RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane361RankCoverGenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
