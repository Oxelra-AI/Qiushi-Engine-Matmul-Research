import QiushiFrozenRank362Bindings00
import QiushiFrozenRank362Bindings01
import QiushiFrozenRank362Bindings02
import QiushiFrozenRank362Bindings03
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane362RankCoverGenSourceQRA (i : Fin 31) :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenSourceBasis i)) (plane362RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane362RankCoverGenBound0000
  | ⟨1, _⟩ => plane362RankCoverGenBound0001
  | ⟨2, _⟩ => plane362RankCoverGenBound0002
  | ⟨3, _⟩ => plane362RankCoverGenBound0003
  | ⟨4, _⟩ => plane362RankCoverGenBound0004
  | ⟨5, _⟩ => plane362RankCoverGenBound0005
  | ⟨6, _⟩ => plane362RankCoverGenBound0006
  | ⟨7, _⟩ => plane362RankCoverGenBound0007
  | ⟨8, _⟩ => plane362RankCoverGenBound0008
  | ⟨9, _⟩ => plane362RankCoverGenBound0009
  | ⟨10, _⟩ => plane362RankCoverGenBound0010
  | ⟨11, _⟩ => plane362RankCoverGenBound0011
  | ⟨12, _⟩ => plane362RankCoverGenBound0012
  | ⟨13, _⟩ => plane362RankCoverGenBound0013
  | ⟨14, _⟩ => plane362RankCoverGenBound0014
  | ⟨15, _⟩ => plane362RankCoverGenBound0015
  | ⟨16, _⟩ => plane362RankCoverGenBound0016
  | ⟨17, _⟩ => plane362RankCoverGenBound0017
  | ⟨18, _⟩ => plane362RankCoverGenBound0018
  | ⟨19, _⟩ => plane362RankCoverGenBound0019
  | ⟨20, _⟩ => plane362RankCoverGenBound0020
  | ⟨21, _⟩ => plane362RankCoverGenBound0021
  | ⟨22, _⟩ => plane362RankCoverGenBound0022
  | ⟨23, _⟩ => plane362RankCoverGenBound0023
  | ⟨24, _⟩ => plane362RankCoverGenBound0024
  | ⟨25, _⟩ => plane362RankCoverGenBound0025
  | ⟨26, _⟩ => plane362RankCoverGenBound0026
  | ⟨27, _⟩ => plane362RankCoverGenBound0027
  | ⟨28, _⟩ => plane362RankCoverGenBound0028
  | ⟨29, _⟩ => plane362RankCoverGenBound0029
  | ⟨30, _⟩ => plane362RankCoverGenBound0030
  | ⟨k + 31, h⟩ => by omega
theorem plane362RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (0 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (0 : Fin 7) = [290, 102, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0001 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (1 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (1 : Fin 7) = [264, 70, 32, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0002 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (2 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (2 : Fin 7) = [258, 76, 42, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0004 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (3 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (3 : Fin 7) = [296, 138, 102, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0005 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (4 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (4 : Fin 7) = [296, 160, 102, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0006 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (5 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (5 : Fin 7) = [296, 166, 102, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0008 (by decide +kernel)
theorem plane362RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis (6 : Fin 7))) 16 := by
  rw [show plane362RankCoverGenDeadBasis (6 : Fin 7) = [296, 172, 102, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane362RankCoverGenSource0009 (by decide +kernel)
theorem plane362RankCoverGenDeadQRA (d : Fin 7) :
    QuotientRankAtLeast (spanCodes (plane362RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane362RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane362RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane362RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane362RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane362RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane362RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane362RankCoverGenDeadBound0006
  | ⟨k + 7, h⟩ => by omega
end QiushiMatmul
