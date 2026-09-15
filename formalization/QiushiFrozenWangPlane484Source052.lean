import QiushiPlane484GenData
import QiushiFrozenWangSpaces052

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane484_source1664 : plane484GenConfig.sourceLb (1664 : Fin 1665) ≤ frozenWangTable.L0 (plane484GenConfig.sourceU (1664 : Fin 1665)) := by
  change plane484GenSourceLb (1664 : Fin 1665) ≤
    frozenWangTable.L0 (spanCodes (plane484GenSourceBasis (1664 : Fin 1665)))
  rw [show plane484GenSourceLb (1664 : Fin 1665) = 9 by decide,
      show plane484GenSourceBasis (1664 : Fin 1665) = [258, 128, 64, 32, 18, 10, 4, 1] by decide]
  exact space1664_lower

theorem plane484_sourceBlock052 (offset : Fin 32)
    (hlt : 52 * 32 + offset.val < 1665) :
    plane484GenConfig.sourceLb (Fin.mk (52 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane484GenConfig.sourceU (Fin.mk (52 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane484_source1664
  | ⟨k + 1, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
