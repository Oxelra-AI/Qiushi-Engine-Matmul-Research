import QiushiGlobalOrbitUnused312Bindings00
import QiushiGlobalOrbitUnused312Bindings01
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane312UnusedGenSourceQRA (i : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenSourceBasis i)) (plane312UnusedGenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane312UnusedGenBound0000
  | ⟨1, _⟩ => plane312UnusedGenBound0001
  | ⟨2, _⟩ => plane312UnusedGenBound0002
  | ⟨3, _⟩ => plane312UnusedGenBound0003
  | ⟨4, _⟩ => plane312UnusedGenBound0004
  | ⟨5, _⟩ => plane312UnusedGenBound0005
  | ⟨6, _⟩ => plane312UnusedGenBound0006
  | ⟨7, _⟩ => plane312UnusedGenBound0007
  | ⟨8, _⟩ => plane312UnusedGenBound0008
  | ⟨9, _⟩ => plane312UnusedGenBound0009
  | ⟨10, _⟩ => plane312UnusedGenBound0010
  | ⟨11, _⟩ => plane312UnusedGenBound0011
  | ⟨12, _⟩ => plane312UnusedGenBound0012
  | ⟨13, _⟩ => plane312UnusedGenBound0013
  | ⟨14, _⟩ => plane312UnusedGenBound0014
  | ⟨15, _⟩ => plane312UnusedGenBound0015
  | ⟨16, _⟩ => plane312UnusedGenBound0016
  | ⟨17, _⟩ => plane312UnusedGenBound0017
  | ⟨18, _⟩ => plane312UnusedGenBound0018
  | ⟨19, _⟩ => plane312UnusedGenBound0019
  | ⟨k + 20, h⟩ => by omega
theorem plane312UnusedGenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (0 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (0 : Fin 14) = [386, 96, 20, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0000 (by decide)
theorem plane312UnusedGenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (1 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (1 : Fin 14) = [386, 96, 22, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0001 (by decide)
theorem plane312UnusedGenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (2 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (2 : Fin 14) = [386, 70, 38, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0002 (by decide)
theorem plane312UnusedGenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (3 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (3 : Fin 14) = [262, 132, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0003 (by decide)
theorem plane312UnusedGenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (4 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (4 : Fin 14) = [260, 134, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0004 (by decide)
theorem plane312UnusedGenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (5 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (5 : Fin 14) = [274, 144, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0005 (by decide)
theorem plane312UnusedGenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (6 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (6 : Fin 14) = [278, 148, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0006 (by decide)
theorem plane312UnusedGenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (7 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (7 : Fin 14) = [276, 150, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0007 (by decide)
theorem plane312UnusedGenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (8 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (8 : Fin 14) = [290, 160, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0008 (by decide)
theorem plane312UnusedGenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (9 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (9 : Fin 14) = [294, 164, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0009 (by decide)
theorem plane312UnusedGenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (10 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (10 : Fin 14) = [306, 176, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0010 (by decide)
theorem plane312UnusedGenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (11 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (11 : Fin 14) = [304, 178, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0011 (by decide)
theorem plane312UnusedGenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (12 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (12 : Fin 14) = [310, 180, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0012 (by decide)
theorem plane312UnusedGenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis (13 : Fin 14))) 16 := by
  rw [show plane312UnusedGenDeadBasis (13 : Fin 14) = [308, 182, 96, 10, 1] from rfl]
  exact quotientRankAtLeast_weaken plane312UnusedGenSource0013 (by decide)
theorem plane312UnusedGenDeadQRA (d : Fin 14) :
    QuotientRankAtLeast (spanCodes (plane312UnusedGenDeadBasis d)) 16 :=
  match d with
  | ⟨0, _⟩ => plane312UnusedGenDeadBound0000
  | ⟨1, _⟩ => plane312UnusedGenDeadBound0001
  | ⟨2, _⟩ => plane312UnusedGenDeadBound0002
  | ⟨3, _⟩ => plane312UnusedGenDeadBound0003
  | ⟨4, _⟩ => plane312UnusedGenDeadBound0004
  | ⟨5, _⟩ => plane312UnusedGenDeadBound0005
  | ⟨6, _⟩ => plane312UnusedGenDeadBound0006
  | ⟨7, _⟩ => plane312UnusedGenDeadBound0007
  | ⟨8, _⟩ => plane312UnusedGenDeadBound0008
  | ⟨9, _⟩ => plane312UnusedGenDeadBound0009
  | ⟨10, _⟩ => plane312UnusedGenDeadBound0010
  | ⟨11, _⟩ => plane312UnusedGenDeadBound0011
  | ⟨12, _⟩ => plane312UnusedGenDeadBound0012
  | ⟨13, _⟩ => plane312UnusedGenDeadBound0013
  | ⟨k + 14, h⟩ => by omega
end QiushiMatmul
