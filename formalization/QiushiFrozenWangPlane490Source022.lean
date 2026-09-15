import QiushiPlane490GenData
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces063
import QiushiFrozenWangSpaces121

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source0704 : plane490GenConfig.sourceLb (704 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (704 : Fin 713)) := by
  change plane490GenSourceLb (704 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (704 : Fin 713)))
  rw [show plane490GenSourceLb (704 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (704 : Fin 713) = [257, 129, 64, 33, 16, 8, 5, 2] by decide]
  exact space3873_lower

theorem plane490_source0705 : plane490GenConfig.sourceLb (705 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (705 : Fin 713)) := by
  change plane490GenSourceLb (705 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (705 : Fin 713)))
  rw [show plane490GenSourceLb (705 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (705 : Fin 713) = [256, 129, 64, 33, 17, 8, 4, 2] by decide]
  exact space1630_lower

theorem plane490_source0706 : plane490GenConfig.sourceLb (706 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (706 : Fin 713)) := by
  change plane490GenSourceLb (706 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (706 : Fin 713)))
  rw [show plane490GenSourceLb (706 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (706 : Fin 713) = [257, 129, 65, 33, 16, 8, 4, 2] by decide]
  exact space2017_lower

theorem plane490_source0707 : plane490GenConfig.sourceLb (707 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (707 : Fin 713)) := by
  change plane490GenSourceLb (707 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (707 : Fin 713)))
  rw [show plane490GenSourceLb (707 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (707 : Fin 713) = [256, 130, 66, 34, 18, 10, 6, 1] by decide]
  exact space1626_lower

theorem plane490_source0708 : plane490GenConfig.sourceLb (708 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (708 : Fin 713)) := by
  change plane490GenSourceLb (708 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (708 : Fin 713)))
  rw [show plane490GenSourceLb (708 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (708 : Fin 713) = [256, 128, 66, 32, 18, 10, 6, 1] by decide]
  exact space1623_lower

theorem plane490_source0709 : plane490GenConfig.sourceLb (709 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (709 : Fin 713)) := by
  change plane490GenSourceLb (709 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (709 : Fin 713)))
  rw [show plane490GenSourceLb (709 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (709 : Fin 713) = [256, 130, 64, 32, 18, 10, 6, 1] by decide]
  exact space1622_lower

theorem plane490_source0710 : plane490GenConfig.sourceLb (710 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (710 : Fin 713)) := by
  change plane490GenSourceLb (710 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (710 : Fin 713)))
  rw [show plane490GenSourceLb (710 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (710 : Fin 713) = [256, 128, 66, 34, 18, 10, 4, 1] by decide]
  exact space1620_lower

theorem plane490_source0711 : plane490GenConfig.sourceLb (711 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (711 : Fin 713)) := by
  change plane490GenSourceLb (711 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (711 : Fin 713)))
  rw [show plane490GenSourceLb (711 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (711 : Fin 713) = [260, 128, 68, 36, 20, 8, 2, 1] by decide]
  exact space2027_lower

theorem plane490_source0712 : plane490GenConfig.sourceLb (712 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (712 : Fin 713)) := by
  change plane490GenSourceLb (712 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (712 : Fin 713)))
  rw [show plane490GenSourceLb (712 : Fin 713) = 9 by decide,
      show plane490GenSourceBasis (712 : Fin 713) = [260, 132, 68, 32, 20, 8, 2, 1] by decide]
  exact space3874_lower

theorem plane490_sourceBlock022 (offset : Fin 32)
    (hlt : 22 * 32 + offset.val < 713) :
    plane490GenConfig.sourceLb (Fin.mk (22 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (Fin.mk (22 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane490_source0704
  | ⟨1, _⟩ => intro hlt; exact plane490_source0705
  | ⟨2, _⟩ => intro hlt; exact plane490_source0706
  | ⟨3, _⟩ => intro hlt; exact plane490_source0707
  | ⟨4, _⟩ => intro hlt; exact plane490_source0708
  | ⟨5, _⟩ => intro hlt; exact plane490_source0709
  | ⟨6, _⟩ => intro hlt; exact plane490_source0710
  | ⟨7, _⟩ => intro hlt; exact plane490_source0711
  | ⟨8, _⟩ => intro hlt; exact plane490_source0712
  | ⟨k + 9, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
