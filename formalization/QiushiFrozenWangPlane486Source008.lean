import QiushiPlane486GenData
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces063
import QiushiFrozenWangSpaces070

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane486_source0256 : plane486GenConfig.sourceLb (256 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (256 : Fin 262)) := by
  change plane486GenSourceLb (256 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (256 : Fin 262)))
  rw [show plane486GenSourceLb (256 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (256 : Fin 262) = [257, 128, 64, 33, 17, 8, 4, 2] by decide]
  exact space1629_lower

theorem plane486_source0257 : plane486GenConfig.sourceLb (257 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (257 : Fin 262)) := by
  change plane486GenSourceLb (257 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (257 : Fin 262)))
  rw [show plane486GenSourceLb (257 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (257 : Fin 262) = [257, 129, 64, 32, 17, 8, 4, 2] by decide]
  exact space1627_lower

theorem plane486_source0258 : plane486GenConfig.sourceLb (258 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (258 : Fin 262)) := by
  change plane486GenSourceLb (258 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (258 : Fin 262)))
  rw [show plane486GenSourceLb (258 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (258 : Fin 262) = [258, 128, 64, 34, 18, 10, 4, 1] by decide]
  exact space1619_lower

theorem plane486_source0259 : plane486GenConfig.sourceLb (259 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (259 : Fin 262)) := by
  change plane486GenSourceLb (259 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (259 : Fin 262)))
  rw [show plane486GenSourceLb (259 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (259 : Fin 262) = [258, 130, 64, 32, 18, 10, 4, 1] by decide]
  exact space1617_lower

theorem plane486_source0260 : plane486GenConfig.sourceLb (260 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (260 : Fin 262)) := by
  change plane486GenSourceLb (260 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (260 : Fin 262)))
  rw [show plane486GenSourceLb (260 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (260 : Fin 262) = [260, 128, 68, 36, 20, 8, 2, 1] by decide]
  exact space2027_lower

theorem plane486_source0261 : plane486GenConfig.sourceLb (261 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (261 : Fin 262)) := by
  change plane486GenSourceLb (261 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (261 : Fin 262)))
  rw [show plane486GenSourceLb (261 : Fin 262) = 3 by decide,
      show plane486GenSourceBasis (261 : Fin 262) = [256, 128, 64, 32, 8, 4, 2, 1] by decide]
  exact space2252_lower

theorem plane486_sourceBlock008 (offset : Fin 32)
    (hlt : 8 * 32 + offset.val < 262) :
    plane486GenConfig.sourceLb (Fin.mk (8 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (Fin.mk (8 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane486_source0256
  | ⟨1, _⟩ => intro hlt; exact plane486_source0257
  | ⟨2, _⟩ => intro hlt; exact plane486_source0258
  | ⟨3, _⟩ => intro hlt; exact plane486_source0259
  | ⟨4, _⟩ => intro hlt; exact plane486_source0260
  | ⟨5, _⟩ => intro hlt; exact plane486_source0261
  | ⟨k + 6, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
