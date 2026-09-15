import QiushiPlane485GenData
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces063

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane485_source0416 : plane485GenConfig.sourceLb (416 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (416 : Fin 421)) := by
  change plane485GenSourceLb (416 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (416 : Fin 421)))
  rw [show plane485GenSourceLb (416 : Fin 421) = 9 by decide,
      show plane485GenSourceBasis (416 : Fin 421) = [258, 128, 64, 34, 18, 10, 6, 1] by decide]
  exact space1660_lower

theorem plane485_source0417 : plane485GenConfig.sourceLb (417 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (417 : Fin 421)) := by
  change plane485GenSourceLb (417 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (417 : Fin 421)))
  rw [show plane485GenSourceLb (417 : Fin 421) = 9 by decide,
      show plane485GenSourceBasis (417 : Fin 421) = [258, 130, 64, 34, 16, 10, 4, 1] by decide]
  exact space2024_lower

theorem plane485_source0418 : plane485GenConfig.sourceLb (418 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (418 : Fin 421)) := by
  change plane485GenSourceLb (418 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (418 : Fin 421)))
  rw [show plane485GenSourceLb (418 : Fin 421) = 9 by decide,
      show plane485GenSourceBasis (418 : Fin 421) = [258, 130, 66, 32, 16, 10, 4, 1] by decide]
  exact space2025_lower

theorem plane485_source0419 : plane485GenConfig.sourceLb (419 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (419 : Fin 421)) := by
  change plane485GenSourceLb (419 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (419 : Fin 421)))
  rw [show plane485GenSourceLb (419 : Fin 421) = 9 by decide,
      show plane485GenSourceBasis (419 : Fin 421) = [258, 128, 64, 32, 16, 10, 4, 1] by decide]
  exact space2026_lower

theorem plane485_source0420 : plane485GenConfig.sourceLb (420 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (420 : Fin 421)) := by
  change plane485GenSourceLb (420 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (420 : Fin 421)))
  rw [show plane485GenSourceLb (420 : Fin 421) = 9 by decide,
      show plane485GenSourceBasis (420 : Fin 421) = [260, 128, 68, 36, 20, 8, 2, 1] by decide]
  exact space2027_lower

theorem plane485_sourceBlock013 (offset : Fin 32)
    (hlt : 13 * 32 + offset.val < 421) :
    plane485GenConfig.sourceLb (Fin.mk (13 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (Fin.mk (13 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane485_source0416
  | ⟨1, _⟩ => intro hlt; exact plane485_source0417
  | ⟨2, _⟩ => intro hlt; exact plane485_source0418
  | ⟨3, _⟩ => intro hlt; exact plane485_source0419
  | ⟨4, _⟩ => intro hlt; exact plane485_source0420
  | ⟨k + 5, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
