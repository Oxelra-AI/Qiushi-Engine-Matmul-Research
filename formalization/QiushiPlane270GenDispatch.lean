import QiushiPlane270GenBindings00
import QiushiPlane270GenBindings01
import QiushiPlane270GenBindings02
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul
theorem plane270GenSourceQRA (i : Fin 22) :
    QuotientRankAtLeast (spanCodes (plane270GenSourceBasis i)) (plane270GenSourceLb i) :=
  match i with
  | ⟨0, _⟩ => plane270GenBound0000
  | ⟨1, _⟩ => plane270GenBound0001
  | ⟨2, _⟩ => plane270GenBound0002
  | ⟨3, _⟩ => plane270GenBound0003
  | ⟨4, _⟩ => plane270GenBound0004
  | ⟨5, _⟩ => plane270GenBound0005
  | ⟨6, _⟩ => plane270GenBound0006
  | ⟨7, _⟩ => plane270GenBound0007
  | ⟨8, _⟩ => plane270GenBound0008
  | ⟨9, _⟩ => plane270GenBound0009
  | ⟨10, _⟩ => plane270GenBound0010
  | ⟨11, _⟩ => plane270GenBound0011
  | ⟨12, _⟩ => plane270GenBound0012
  | ⟨13, _⟩ => plane270GenBound0013
  | ⟨14, _⟩ => plane270GenBound0014
  | ⟨15, _⟩ => plane270GenBound0015
  | ⟨16, _⟩ => plane270GenBound0016
  | ⟨17, _⟩ => plane270GenBound0017
  | ⟨18, _⟩ => plane270GenBound0018
  | ⟨19, _⟩ => plane270GenBound0019
  | ⟨20, _⟩ => plane270GenBound0020
  | ⟨21, _⟩ => plane270GenBound0021
  | ⟨k + 22, h⟩ => by omega
theorem plane270GenDeadBound0000 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (0 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (0 : Fin 20) = [320, 32, 12, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0000 (by decide)
theorem plane270GenDeadBound0001 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (1 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (1 : Fin 20) = [320, 32, 20, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0001 (by decide)
theorem plane270GenDeadBound0002 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (2 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (2 : Fin 20) = [320, 32, 28, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0002 (by decide)
theorem plane270GenDeadBound0003 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (3 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (3 : Fin 20) = [260, 68, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0003 (by decide)
theorem plane270GenDeadBound0004 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (4 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (4 : Fin 20) = [264, 72, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0004 (by decide)
theorem plane270GenDeadBound0005 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (5 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (5 : Fin 20) = [268, 76, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0005 (by decide)
theorem plane270GenDeadBound0006 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (6 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (6 : Fin 20) = [272, 80, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0006 (by decide)
theorem plane270GenDeadBound0007 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (7 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (7 : Fin 20) = [276, 84, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0007 (by decide)
theorem plane270GenDeadBound0008 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (8 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (8 : Fin 20) = [280, 88, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0008 (by decide)
theorem plane270GenDeadBound0009 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (9 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (9 : Fin 20) = [284, 92, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0009 (by decide)
theorem plane270GenDeadBound0010 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (10 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (10 : Fin 20) = [320, 132, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0010 (by decide)
theorem plane270GenDeadBound0011 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (11 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (11 : Fin 20) = [320, 136, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0011 (by decide)
theorem plane270GenDeadBound0012 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (12 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (12 : Fin 20) = [320, 140, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0012 (by decide)
theorem plane270GenDeadBound0013 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (13 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (13 : Fin 20) = [320, 148, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0013 (by decide)
theorem plane270GenDeadBound0014 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (14 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (14 : Fin 20) = [320, 156, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0014 (by decide)
theorem plane270GenDeadBound0015 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (15 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (15 : Fin 20) = [320, 196, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0015 (by decide)
theorem plane270GenDeadBound0016 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (16 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (16 : Fin 20) = [320, 200, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0016 (by decide)
theorem plane270GenDeadBound0017 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (17 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (17 : Fin 20) = [320, 204, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0017 (by decide)
theorem plane270GenDeadBound0018 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (18 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (18 : Fin 20) = [320, 212, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0018 (by decide)
theorem plane270GenDeadBound0019 :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis (19 : Fin 20))) 14 := by
  rw [show plane270GenDeadBasis (19 : Fin 20) = [320, 220, 32, 2, 1] from rfl]
  exact quotientRankAtLeast_weaken plane270GenSource0019 (by decide)
theorem plane270GenDeadQRA (d : Fin 20) :
    QuotientRankAtLeast (spanCodes (plane270GenDeadBasis d)) 14 :=
  match d with
  | ⟨0, _⟩ => plane270GenDeadBound0000
  | ⟨1, _⟩ => plane270GenDeadBound0001
  | ⟨2, _⟩ => plane270GenDeadBound0002
  | ⟨3, _⟩ => plane270GenDeadBound0003
  | ⟨4, _⟩ => plane270GenDeadBound0004
  | ⟨5, _⟩ => plane270GenDeadBound0005
  | ⟨6, _⟩ => plane270GenDeadBound0006
  | ⟨7, _⟩ => plane270GenDeadBound0007
  | ⟨8, _⟩ => plane270GenDeadBound0008
  | ⟨9, _⟩ => plane270GenDeadBound0009
  | ⟨10, _⟩ => plane270GenDeadBound0010
  | ⟨11, _⟩ => plane270GenDeadBound0011
  | ⟨12, _⟩ => plane270GenDeadBound0012
  | ⟨13, _⟩ => plane270GenDeadBound0013
  | ⟨14, _⟩ => plane270GenDeadBound0014
  | ⟨15, _⟩ => plane270GenDeadBound0015
  | ⟨16, _⟩ => plane270GenDeadBound0016
  | ⟨17, _⟩ => plane270GenDeadBound0017
  | ⟨18, _⟩ => plane270GenDeadBound0018
  | ⟨19, _⟩ => plane270GenDeadBound0019
  | ⟨k + 20, h⟩ => by omega
end QiushiMatmul
