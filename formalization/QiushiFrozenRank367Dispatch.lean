import QiushiFrozenRank367Bindings00
import QiushiFrozenRank367Bindings01
import QiushiFrozenRank367Bindings02
import QiushiFrozenRank367Bindings03
import QiushiFrozenRank367Bindings04
import QiushiFrozenRank367Bindings05
import QiushiFrozenRank367Bindings06
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane367RankCoverGenSourceQRA (i : Fin 70) :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenSourceBasis i)) (plane367RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane367RankCoverGenBound0000
  | ⟨1, _⟩ => plane367RankCoverGenBound0001
  | ⟨2, _⟩ => plane367RankCoverGenBound0002
  | ⟨3, _⟩ => plane367RankCoverGenBound0003
  | ⟨4, _⟩ => plane367RankCoverGenBound0004
  | ⟨5, _⟩ => plane367RankCoverGenBound0005
  | ⟨6, _⟩ => plane367RankCoverGenBound0006
  | ⟨7, _⟩ => plane367RankCoverGenBound0007
  | ⟨8, _⟩ => plane367RankCoverGenBound0008
  | ⟨9, _⟩ => plane367RankCoverGenBound0009
  | ⟨10, _⟩ => plane367RankCoverGenBound0010
  | ⟨11, _⟩ => plane367RankCoverGenBound0011
  | ⟨12, _⟩ => plane367RankCoverGenBound0012
  | ⟨13, _⟩ => plane367RankCoverGenBound0013
  | ⟨14, _⟩ => plane367RankCoverGenBound0014
  | ⟨15, _⟩ => plane367RankCoverGenBound0015
  | ⟨16, _⟩ => plane367RankCoverGenBound0016
  | ⟨17, _⟩ => plane367RankCoverGenBound0017
  | ⟨18, _⟩ => plane367RankCoverGenBound0018
  | ⟨19, _⟩ => plane367RankCoverGenBound0019
  | ⟨20, _⟩ => plane367RankCoverGenBound0020
  | ⟨21, _⟩ => plane367RankCoverGenBound0021
  | ⟨22, _⟩ => plane367RankCoverGenBound0022
  | ⟨23, _⟩ => plane367RankCoverGenBound0023
  | ⟨24, _⟩ => plane367RankCoverGenBound0024
  | ⟨25, _⟩ => plane367RankCoverGenBound0025
  | ⟨26, _⟩ => plane367RankCoverGenBound0026
  | ⟨27, _⟩ => plane367RankCoverGenBound0027
  | ⟨28, _⟩ => plane367RankCoverGenBound0028
  | ⟨29, _⟩ => plane367RankCoverGenBound0029
  | ⟨30, _⟩ => plane367RankCoverGenBound0030
  | ⟨31, _⟩ => plane367RankCoverGenBound0031
  | ⟨32, _⟩ => plane367RankCoverGenBound0032
  | ⟨33, _⟩ => plane367RankCoverGenBound0033
  | ⟨34, _⟩ => plane367RankCoverGenBound0034
  | ⟨35, _⟩ => plane367RankCoverGenBound0035
  | ⟨36, _⟩ => plane367RankCoverGenBound0036
  | ⟨37, _⟩ => plane367RankCoverGenBound0037
  | ⟨38, _⟩ => plane367RankCoverGenBound0038
  | ⟨39, _⟩ => plane367RankCoverGenBound0039
  | ⟨40, _⟩ => plane367RankCoverGenBound0040
  | ⟨41, _⟩ => plane367RankCoverGenBound0041
  | ⟨42, _⟩ => plane367RankCoverGenBound0042
  | ⟨43, _⟩ => plane367RankCoverGenBound0043
  | ⟨44, _⟩ => plane367RankCoverGenBound0044
  | ⟨45, _⟩ => plane367RankCoverGenBound0045
  | ⟨46, _⟩ => plane367RankCoverGenBound0046
  | ⟨47, _⟩ => plane367RankCoverGenBound0047
  | ⟨48, _⟩ => plane367RankCoverGenBound0048
  | ⟨49, _⟩ => plane367RankCoverGenBound0049
  | ⟨50, _⟩ => plane367RankCoverGenBound0050
  | ⟨51, _⟩ => plane367RankCoverGenBound0051
  | ⟨52, _⟩ => plane367RankCoverGenBound0052
  | ⟨53, _⟩ => plane367RankCoverGenBound0053
  | ⟨54, _⟩ => plane367RankCoverGenBound0054
  | ⟨55, _⟩ => plane367RankCoverGenBound0055
  | ⟨56, _⟩ => plane367RankCoverGenBound0056
  | ⟨57, _⟩ => plane367RankCoverGenBound0057
  | ⟨58, _⟩ => plane367RankCoverGenBound0058
  | ⟨59, _⟩ => plane367RankCoverGenBound0059
  | ⟨60, _⟩ => plane367RankCoverGenBound0060
  | ⟨61, _⟩ => plane367RankCoverGenBound0061
  | ⟨62, _⟩ => plane367RankCoverGenBound0062
  | ⟨63, _⟩ => plane367RankCoverGenBound0063
  | ⟨64, _⟩ => plane367RankCoverGenBound0064
  | ⟨65, _⟩ => plane367RankCoverGenBound0065
  | ⟨66, _⟩ => plane367RankCoverGenBound0066
  | ⟨67, _⟩ => plane367RankCoverGenBound0067
  | ⟨68, _⟩ => plane367RankCoverGenBound0068
  | ⟨69, _⟩ => plane367RankCoverGenBound0069
  | ⟨k + 70, h⟩ => by omega
theorem plane367RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (0 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (0 : Fin 7) = [270, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0007 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (1 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (1 : Fin 7) = [270, 160, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0008 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (2 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (2 : Fin 7) = [270, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0010 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (3 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (3 : Fin 7) = [270, 160, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0011 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (4 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (4 : Fin 7) = [270, 160, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0012 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (5 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (5 : Fin 7) = [270, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0013 (by decide +kernel)
theorem plane367RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis (6 : Fin 7))) 16 := by
  rw [show plane367RankCoverGenDeadBasis (6 : Fin 7) = [270, 160, 106, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane367RankCoverGenSource0014 (by decide +kernel)
theorem plane367RankCoverGenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane367RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane367RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane367RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane367RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane367RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane367RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane367RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane367RankCoverGenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
