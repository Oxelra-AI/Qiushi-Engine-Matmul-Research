import QiushiFrozenRank369Bindings00
import QiushiFrozenRank369Bindings01
import QiushiFrozenRank369Bindings02
import QiushiFrozenRank369Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane369RankCoverGenSourceQRA (i : Fin 37) :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenSourceBasis i)) (plane369RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane369RankCoverGenBound0000
  | ⟨1, _⟩ => plane369RankCoverGenBound0001
  | ⟨2, _⟩ => plane369RankCoverGenBound0002
  | ⟨3, _⟩ => plane369RankCoverGenBound0003
  | ⟨4, _⟩ => plane369RankCoverGenBound0004
  | ⟨5, _⟩ => plane369RankCoverGenBound0005
  | ⟨6, _⟩ => plane369RankCoverGenBound0006
  | ⟨7, _⟩ => plane369RankCoverGenBound0007
  | ⟨8, _⟩ => plane369RankCoverGenBound0008
  | ⟨9, _⟩ => plane369RankCoverGenBound0009
  | ⟨10, _⟩ => plane369RankCoverGenBound0010
  | ⟨11, _⟩ => plane369RankCoverGenBound0011
  | ⟨12, _⟩ => plane369RankCoverGenBound0012
  | ⟨13, _⟩ => plane369RankCoverGenBound0013
  | ⟨14, _⟩ => plane369RankCoverGenBound0014
  | ⟨15, _⟩ => plane369RankCoverGenBound0015
  | ⟨16, _⟩ => plane369RankCoverGenBound0016
  | ⟨17, _⟩ => plane369RankCoverGenBound0017
  | ⟨18, _⟩ => plane369RankCoverGenBound0018
  | ⟨19, _⟩ => plane369RankCoverGenBound0019
  | ⟨20, _⟩ => plane369RankCoverGenBound0020
  | ⟨21, _⟩ => plane369RankCoverGenBound0021
  | ⟨22, _⟩ => plane369RankCoverGenBound0022
  | ⟨23, _⟩ => plane369RankCoverGenBound0023
  | ⟨24, _⟩ => plane369RankCoverGenBound0024
  | ⟨25, _⟩ => plane369RankCoverGenBound0025
  | ⟨26, _⟩ => plane369RankCoverGenBound0026
  | ⟨27, _⟩ => plane369RankCoverGenBound0027
  | ⟨28, _⟩ => plane369RankCoverGenBound0028
  | ⟨29, _⟩ => plane369RankCoverGenBound0029
  | ⟨30, _⟩ => plane369RankCoverGenBound0030
  | ⟨31, _⟩ => plane369RankCoverGenBound0031
  | ⟨32, _⟩ => plane369RankCoverGenBound0032
  | ⟨33, _⟩ => plane369RankCoverGenBound0033
  | ⟨34, _⟩ => plane369RankCoverGenBound0034
  | ⟨35, _⟩ => plane369RankCoverGenBound0035
  | ⟨36, _⟩ => plane369RankCoverGenBound0036
  | ⟨k + 37, h⟩ => by omega
theorem plane369RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (0 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (0 : Fin 8) = [326, 160, 20, 14, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0001 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (1 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (1 : Fin 8) = [256, 160, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0005 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (2 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (2 : Fin 8) = [268, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0006 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (3 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (3 : Fin 8) = [266, 160, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0007 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (4 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (4 : Fin 8) = [290, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0008 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (5 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (5 : Fin 8) = [302, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0009 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (6 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (6 : Fin 8) = [300, 160, 106, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0010 (by decide +kernel)
theorem plane369RankCoverGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis (7 : Fin 8))) 16 := by
  rw [show plane369RankCoverGenDeadBasis (7 : Fin 8) = [296, 160, 110, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane369RankCoverGenSource0011 (by decide +kernel)
theorem plane369RankCoverGenDeadQRA (d : Fin 8) :
    QuotientRankAtLeast (spanCodes (plane369RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane369RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane369RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane369RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane369RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane369RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane369RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane369RankCoverGenDeadBound0006
  | ⟨7, _⟩ => plane369RankCoverGenDeadBound0007
  | ⟨k + 8, h⟩ => by omega
end QiushiMatmul
