import QiushiFrozenRank363Bindings00
import QiushiFrozenRank363Bindings01
import QiushiFrozenRank363Bindings02
import QiushiFrozenRank363Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane363RankCoverGenSourceQRA (i : Fin 33) :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenSourceBasis i)) (plane363RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane363RankCoverGenBound0000
  | ⟨1, _⟩ => plane363RankCoverGenBound0001
  | ⟨2, _⟩ => plane363RankCoverGenBound0002
  | ⟨3, _⟩ => plane363RankCoverGenBound0003
  | ⟨4, _⟩ => plane363RankCoverGenBound0004
  | ⟨5, _⟩ => plane363RankCoverGenBound0005
  | ⟨6, _⟩ => plane363RankCoverGenBound0006
  | ⟨7, _⟩ => plane363RankCoverGenBound0007
  | ⟨8, _⟩ => plane363RankCoverGenBound0008
  | ⟨9, _⟩ => plane363RankCoverGenBound0009
  | ⟨10, _⟩ => plane363RankCoverGenBound0010
  | ⟨11, _⟩ => plane363RankCoverGenBound0011
  | ⟨12, _⟩ => plane363RankCoverGenBound0012
  | ⟨13, _⟩ => plane363RankCoverGenBound0013
  | ⟨14, _⟩ => plane363RankCoverGenBound0014
  | ⟨15, _⟩ => plane363RankCoverGenBound0015
  | ⟨16, _⟩ => plane363RankCoverGenBound0016
  | ⟨17, _⟩ => plane363RankCoverGenBound0017
  | ⟨18, _⟩ => plane363RankCoverGenBound0018
  | ⟨19, _⟩ => plane363RankCoverGenBound0019
  | ⟨20, _⟩ => plane363RankCoverGenBound0020
  | ⟨21, _⟩ => plane363RankCoverGenBound0021
  | ⟨22, _⟩ => plane363RankCoverGenBound0022
  | ⟨23, _⟩ => plane363RankCoverGenBound0023
  | ⟨24, _⟩ => plane363RankCoverGenBound0024
  | ⟨25, _⟩ => plane363RankCoverGenBound0025
  | ⟨26, _⟩ => plane363RankCoverGenBound0026
  | ⟨27, _⟩ => plane363RankCoverGenBound0027
  | ⟨28, _⟩ => plane363RankCoverGenBound0028
  | ⟨29, _⟩ => plane363RankCoverGenBound0029
  | ⟨30, _⟩ => plane363RankCoverGenBound0030
  | ⟨31, _⟩ => plane363RankCoverGenBound0031
  | ⟨32, _⟩ => plane363RankCoverGenBound0032
  | ⟨k + 33, h⟩ => by omega
theorem plane363RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (0 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (0 : Fin 13) = [262, 160, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0000 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (1 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (1 : Fin 13) = [262, 160, 20, 12, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0001 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (2 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (2 : Fin 13) = [262, 138, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0005 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (3 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (3 : Fin 13) = [262, 142, 46, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0006 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (4 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (4 : Fin 13) = [262, 160, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0007 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (5 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (5 : Fin 13) = [262, 160, 70, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0008 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (6 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (6 : Fin 13) = [262, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0009 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (7 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (7 : Fin 13) = [262, 160, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0010 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (8 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (8 : Fin 13) = [262, 160, 98, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0011 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (9 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (9 : Fin 13) = [262, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0012 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (10 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (10 : Fin 13) = [262, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0013 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (11 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (11 : Fin 13) = [262, 160, 106, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0014 (by decide +kernel)
theorem plane363RankCoverGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis (12 : Fin 13))) 16 := by
  rw [show plane363RankCoverGenDeadBasis (12 : Fin 13) = [262, 160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane363RankCoverGenSource0019 (by decide +kernel)
theorem plane363RankCoverGenDeadQRA (d : Fin 13) :
    QuotientRankAtLeast (spanCodes (plane363RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane363RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane363RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane363RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane363RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane363RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane363RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane363RankCoverGenDeadBound0006
  | ⟨7, _⟩ => plane363RankCoverGenDeadBound0007
  | ⟨8, _⟩ => plane363RankCoverGenDeadBound0008
  | ⟨9, _⟩ => plane363RankCoverGenDeadBound0009
  | ⟨10, _⟩ => plane363RankCoverGenDeadBound0010
  | ⟨11, _⟩ => plane363RankCoverGenDeadBound0011
  | ⟨12, _⟩ => plane363RankCoverGenDeadBound0012
  | ⟨k + 13, h⟩ => by omega
end QiushiMatmul
