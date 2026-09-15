import QiushiFrozenRank368Bindings00
import QiushiFrozenRank368Bindings01
import QiushiFrozenRank368Bindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane368RankCoverGenSourceQRA (i : Fin 25) :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenSourceBasis i)) (plane368RankCoverGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane368RankCoverGenBound0000
  | ⟨1, _⟩ => plane368RankCoverGenBound0001
  | ⟨2, _⟩ => plane368RankCoverGenBound0002
  | ⟨3, _⟩ => plane368RankCoverGenBound0003
  | ⟨4, _⟩ => plane368RankCoverGenBound0004
  | ⟨5, _⟩ => plane368RankCoverGenBound0005
  | ⟨6, _⟩ => plane368RankCoverGenBound0006
  | ⟨7, _⟩ => plane368RankCoverGenBound0007
  | ⟨8, _⟩ => plane368RankCoverGenBound0008
  | ⟨9, _⟩ => plane368RankCoverGenBound0009
  | ⟨10, _⟩ => plane368RankCoverGenBound0010
  | ⟨11, _⟩ => plane368RankCoverGenBound0011
  | ⟨12, _⟩ => plane368RankCoverGenBound0012
  | ⟨13, _⟩ => plane368RankCoverGenBound0013
  | ⟨14, _⟩ => plane368RankCoverGenBound0014
  | ⟨15, _⟩ => plane368RankCoverGenBound0015
  | ⟨16, _⟩ => plane368RankCoverGenBound0016
  | ⟨17, _⟩ => plane368RankCoverGenBound0017
  | ⟨18, _⟩ => plane368RankCoverGenBound0018
  | ⟨19, _⟩ => plane368RankCoverGenBound0019
  | ⟨20, _⟩ => plane368RankCoverGenBound0020
  | ⟨21, _⟩ => plane368RankCoverGenBound0021
  | ⟨22, _⟩ => plane368RankCoverGenBound0022
  | ⟨23, _⟩ => plane368RankCoverGenBound0023
  | ⟨24, _⟩ => plane368RankCoverGenBound0024
  | ⟨k + 25, h⟩ => by omega
theorem plane368RankCoverGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (0 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (0 : Fin 12) = [322, 160, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0001 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (1 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (1 : Fin 12) = [322, 136, 40, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0003 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (2 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (2 : Fin 12) = [256, 160, 66, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0004 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (3 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (3 : Fin 12) = [262, 160, 68, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0005 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (4 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (4 : Fin 12) = [264, 160, 74, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0006 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (5 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (5 : Fin 12) = [270, 160, 76, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0007 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (6 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (6 : Fin 12) = [268, 160, 78, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0008 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (7 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (7 : Fin 12) = [290, 160, 96, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0009 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (8 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (8 : Fin 12) = [294, 160, 100, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0011 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (9 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (9 : Fin 12) = [298, 160, 104, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0012 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (10 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (10 : Fin 12) = [296, 160, 106, 20, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0013 (by decide +kernel)
theorem plane368RankCoverGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis (11 : Fin 12))) 16 := by
  rw [show plane368RankCoverGenDeadBasis (11 : Fin 12) = [262, 160, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane368RankCoverGenSource0018 (by decide +kernel)
theorem plane368RankCoverGenDeadQRA (d : Fin 12) :
    QuotientRankAtLeast (spanCodes (plane368RankCoverGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane368RankCoverGenDeadBound0000
  | ⟨1, _⟩ => plane368RankCoverGenDeadBound0001
  | ⟨2, _⟩ => plane368RankCoverGenDeadBound0002
  | ⟨3, _⟩ => plane368RankCoverGenDeadBound0003
  | ⟨4, _⟩ => plane368RankCoverGenDeadBound0004
  | ⟨5, _⟩ => plane368RankCoverGenDeadBound0005
  | ⟨6, _⟩ => plane368RankCoverGenDeadBound0006
  | ⟨7, _⟩ => plane368RankCoverGenDeadBound0007
  | ⟨8, _⟩ => plane368RankCoverGenDeadBound0008
  | ⟨9, _⟩ => plane368RankCoverGenDeadBound0009
  | ⟨10, _⟩ => plane368RankCoverGenDeadBound0010
  | ⟨11, _⟩ => plane368RankCoverGenDeadBound0011
  | ⟨k + 12, h⟩ => by omega
end QiushiMatmul
