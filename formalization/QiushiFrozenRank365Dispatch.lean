import QiushiFrozenRank365Bindings00
import QiushiFrozenRank365Bindings01
import QiushiFrozenRank365Bindings02
import QiushiFrozenRank365Bindings03
import QiushiFrozenRank365Bindings04
import QiushiFrozenRank365Bindings05
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane365RankCoverGenSourceQRA (i : Fin 52) :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenSourceBasis i)) (plane365RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane365RankCoverGenBound0000
  | ⟨1, _⟩ => plane365RankCoverGenBound0001
  | ⟨2, _⟩ => plane365RankCoverGenBound0002
  | ⟨3, _⟩ => plane365RankCoverGenBound0003
  | ⟨4, _⟩ => plane365RankCoverGenBound0004
  | ⟨5, _⟩ => plane365RankCoverGenBound0005
  | ⟨6, _⟩ => plane365RankCoverGenBound0006
  | ⟨7, _⟩ => plane365RankCoverGenBound0007
  | ⟨8, _⟩ => plane365RankCoverGenBound0008
  | ⟨9, _⟩ => plane365RankCoverGenBound0009
  | ⟨10, _⟩ => plane365RankCoverGenBound0010
  | ⟨11, _⟩ => plane365RankCoverGenBound0011
  | ⟨12, _⟩ => plane365RankCoverGenBound0012
  | ⟨13, _⟩ => plane365RankCoverGenBound0013
  | ⟨14, _⟩ => plane365RankCoverGenBound0014
  | ⟨15, _⟩ => plane365RankCoverGenBound0015
  | ⟨16, _⟩ => plane365RankCoverGenBound0016
  | ⟨17, _⟩ => plane365RankCoverGenBound0017
  | ⟨18, _⟩ => plane365RankCoverGenBound0018
  | ⟨19, _⟩ => plane365RankCoverGenBound0019
  | ⟨20, _⟩ => plane365RankCoverGenBound0020
  | ⟨21, _⟩ => plane365RankCoverGenBound0021
  | ⟨22, _⟩ => plane365RankCoverGenBound0022
  | ⟨23, _⟩ => plane365RankCoverGenBound0023
  | ⟨24, _⟩ => plane365RankCoverGenBound0024
  | ⟨25, _⟩ => plane365RankCoverGenBound0025
  | ⟨26, _⟩ => plane365RankCoverGenBound0026
  | ⟨27, _⟩ => plane365RankCoverGenBound0027
  | ⟨28, _⟩ => plane365RankCoverGenBound0028
  | ⟨29, _⟩ => plane365RankCoverGenBound0029
  | ⟨30, _⟩ => plane365RankCoverGenBound0030
  | ⟨31, _⟩ => plane365RankCoverGenBound0031
  | ⟨32, _⟩ => plane365RankCoverGenBound0032
  | ⟨33, _⟩ => plane365RankCoverGenBound0033
  | ⟨34, _⟩ => plane365RankCoverGenBound0034
  | ⟨35, _⟩ => plane365RankCoverGenBound0035
  | ⟨36, _⟩ => plane365RankCoverGenBound0036
  | ⟨37, _⟩ => plane365RankCoverGenBound0037
  | ⟨38, _⟩ => plane365RankCoverGenBound0038
  | ⟨39, _⟩ => plane365RankCoverGenBound0039
  | ⟨40, _⟩ => plane365RankCoverGenBound0040
  | ⟨41, _⟩ => plane365RankCoverGenBound0041
  | ⟨42, _⟩ => plane365RankCoverGenBound0042
  | ⟨43, _⟩ => plane365RankCoverGenBound0043
  | ⟨44, _⟩ => plane365RankCoverGenBound0044
  | ⟨45, _⟩ => plane365RankCoverGenBound0045
  | ⟨46, _⟩ => plane365RankCoverGenBound0046
  | ⟨47, _⟩ => plane365RankCoverGenBound0047
  | ⟨48, _⟩ => plane365RankCoverGenBound0048
  | ⟨49, _⟩ => plane365RankCoverGenBound0049
  | ⟨50, _⟩ => plane365RankCoverGenBound0050
  | ⟨51, _⟩ => plane365RankCoverGenBound0051
  | ⟨k + 52, h⟩ => by omega
theorem plane365RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (0 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (0 : Fin 8) = [262, 160, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0001 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (1 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (1 : Fin 8) = [266, 136, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0005 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (2 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (2 : Fin 8) = [266, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0008 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (3 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (3 : Fin 8) = [266, 160, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0009 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (4 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (4 : Fin 8) = [266, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0010 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (5 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (5 : Fin 8) = [266, 160, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0011 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (6 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (6 : Fin 8) = [266, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0012 (by decide +kernel)
theorem plane365RankCoverGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis (7 : Fin 8))) 16 := by
  rw [show plane365RankCoverGenDeadBasis (7 : Fin 8) = [266, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane365RankCoverGenSource0013 (by decide +kernel)
theorem plane365RankCoverGenDeadQRA (d : Fin 8) :
    QuotientRankAtLeast (spanCodes (plane365RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane365RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane365RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane365RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane365RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane365RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane365RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane365RankCoverGenDeadBound0006
  | ⟨7, _⟩ => plane365RankCoverGenDeadBound0007
  | ⟨k + 8, h⟩ => by omega
end QiushiMatmul
