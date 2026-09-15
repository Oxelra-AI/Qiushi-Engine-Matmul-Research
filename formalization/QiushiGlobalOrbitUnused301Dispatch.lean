import QiushiGlobalOrbitUnused301Bindings00
import QiushiGlobalOrbitUnused301Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane301UnusedGenSourceQRA (i : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenSourceBasis i)) (plane301UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane301UnusedGenBound0000
  | ⟨1, _⟩ => plane301UnusedGenBound0001
  | ⟨2, _⟩ => plane301UnusedGenBound0002
  | ⟨3, _⟩ => plane301UnusedGenBound0003
  | ⟨4, _⟩ => plane301UnusedGenBound0004
  | ⟨5, _⟩ => plane301UnusedGenBound0005
  | ⟨6, _⟩ => plane301UnusedGenBound0006
  | ⟨7, _⟩ => plane301UnusedGenBound0007
  | ⟨8, _⟩ => plane301UnusedGenBound0008
  | ⟨9, _⟩ => plane301UnusedGenBound0009
  | ⟨10, _⟩ => plane301UnusedGenBound0010
  | ⟨11, _⟩ => plane301UnusedGenBound0011
  | ⟨12, _⟩ => plane301UnusedGenBound0012
  | ⟨13, _⟩ => plane301UnusedGenBound0013
  | ⟨14, _⟩ => plane301UnusedGenBound0014
  | ⟨15, _⟩ => plane301UnusedGenBound0015
  | ⟨16, _⟩ => plane301UnusedGenBound0016
  | ⟨17, _⟩ => plane301UnusedGenBound0017
  | ⟨18, _⟩ => plane301UnusedGenBound0018
  | ⟨19, _⟩ => plane301UnusedGenBound0019
  | ⟨k + 20, h⟩ => by omega
theorem plane301UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (0 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (0 : Fin 18) = [160, 68, 16, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0000 (by decide)
theorem plane301UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (1 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (1 : Fin 18) = [164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0001 (by decide)
theorem plane301UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (2 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (2 : Fin 18) = [166, 68, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0002 (by decide)
theorem plane301UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (3 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (3 : Fin 18) = [258, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0004 (by decide)
theorem plane301UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (4 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (4 : Fin 18) = [260, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0005 (by decide)
theorem plane301UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (5 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (5 : Fin 18) = [262, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0006 (by decide)
theorem plane301UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (6 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (6 : Fin 18) = [272, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0007 (by decide)
theorem plane301UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (7 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (7 : Fin 18) = [274, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0008 (by decide)
theorem plane301UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (8 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (8 : Fin 18) = [288, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0009 (by decide)
theorem plane301UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (9 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (9 : Fin 18) = [290, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0010 (by decide)
theorem plane301UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (10 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (10 : Fin 18) = [292, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0011 (by decide)
theorem plane301UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (11 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (11 : Fin 18) = [294, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0012 (by decide)
theorem plane301UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (12 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (12 : Fin 18) = [304, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0013 (by decide)
theorem plane301UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (13 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (13 : Fin 18) = [306, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0014 (by decide)
theorem plane301UnusedGenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (14 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (14 : Fin 18) = [308, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0015 (by decide)
theorem plane301UnusedGenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (15 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (15 : Fin 18) = [310, 176, 68, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0016 (by decide)
theorem plane301UnusedGenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (16 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (16 : Fin 18) = [258, 164, 68, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0017 (by decide)
theorem plane301UnusedGenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis (17 : Fin 18))) 16 := by
  rw [show plane301UnusedGenDeadBasis (17 : Fin 18) = [258, 166, 68, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane301UnusedGenSource0018 (by decide)
theorem plane301UnusedGenDeadQRA (d : Fin 18) :
    QuotientRankAtLeast (spanCodes (plane301UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane301UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane301UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane301UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane301UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane301UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane301UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane301UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane301UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane301UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane301UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane301UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane301UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane301UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane301UnusedGenDeadBound0013
  | ⟨14, _⟩ => plane301UnusedGenDeadBound0014
  | ⟨15, _⟩ => plane301UnusedGenDeadBound0015
  | ⟨16, _⟩ => plane301UnusedGenDeadBound0016
  | ⟨17, _⟩ => plane301UnusedGenDeadBound0017
  | ⟨k + 18, h⟩ => by omega
end QiushiMatmul
