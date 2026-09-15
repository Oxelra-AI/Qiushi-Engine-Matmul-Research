import QiushiPlane489GenData
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces063
import QiushiFrozenWangSpaces070
import QiushiFrozenWangSpaces105
import QiushiFrozenWangSpaces106

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane489_source0352 : plane489GenConfig.sourceLb (352 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (352 : Fin 371)) := by
  change plane489GenSourceLb (352 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (352 : Fin 371)))
  rw [show plane489GenSourceLb (352 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (352 : Fin 371) = [256, 129, 64, 33, 16, 8, 4, 2] by decide]
  exact space2016_lower

theorem plane489_source0353 : plane489GenConfig.sourceLb (353 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (353 : Fin 371)) := by
  change plane489GenSourceLb (353 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (353 : Fin 371)))
  rw [show plane489GenSourceLb (353 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (353 : Fin 371) = [256, 129, 65, 33, 17, 8, 4, 2] by decide]
  exact space1655_lower

theorem plane489_source0354 : plane489GenConfig.sourceLb (354 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (354 : Fin 371)) := by
  change plane489GenSourceLb (354 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (354 : Fin 371)))
  rw [show plane489GenSourceLb (354 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (354 : Fin 371) = [256, 129, 64, 33, 17, 8, 5, 2] by decide]
  exact space1651_lower

theorem plane489_source0355 : plane489GenConfig.sourceLb (355 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (355 : Fin 371)) := by
  change plane489GenSourceLb (355 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (355 : Fin 371)))
  rw [show plane489GenSourceLb (355 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (355 : Fin 371) = [257, 129, 65, 33, 16, 9, 4, 3] by decide]
  exact space1643_lower

theorem plane489_source0356 : plane489GenConfig.sourceLb (356 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (356 : Fin 371)) := by
  change plane489GenSourceLb (356 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (356 : Fin 371)))
  rw [show plane489GenSourceLb (356 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (356 : Fin 371) = [257, 129, 64, 33, 17, 9, 4, 3] by decide]
  exact space2250_lower

theorem plane489_source0357 : plane489GenConfig.sourceLb (357 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (357 : Fin 371)) := by
  change plane489GenSourceLb (357 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (357 : Fin 371)))
  rw [show plane489GenSourceLb (357 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (357 : Fin 371) = [257, 129, 64, 33, 16, 9, 5, 3] by decide]
  exact space1640_lower

theorem plane489_source0358 : plane489GenConfig.sourceLb (358 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (358 : Fin 371)) := by
  change plane489GenSourceLb (358 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (358 : Fin 371)))
  rw [show plane489GenSourceLb (358 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (358 : Fin 371) = [257, 128, 65, 32, 17, 9, 5, 3] by decide]
  exact space2019_lower

theorem plane489_source0359 : plane489GenConfig.sourceLb (359 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (359 : Fin 371)) := by
  change plane489GenSourceLb (359 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (359 : Fin 371)))
  rw [show plane489GenSourceLb (359 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (359 : Fin 371) = [257, 128, 64, 33, 16, 9, 5, 3] by decide]
  exact space1637_lower

theorem plane489_source0360 : plane489GenConfig.sourceLb (360 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (360 : Fin 371)) := by
  change plane489GenSourceLb (360 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (360 : Fin 371)))
  rw [show plane489GenSourceLb (360 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (360 : Fin 371) = [257, 128, 65, 32, 16, 9, 5, 3] by decide]
  exact space1635_lower

theorem plane489_source0361 : plane489GenConfig.sourceLb (361 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (361 : Fin 371)) := by
  change plane489GenSourceLb (361 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (361 : Fin 371)))
  rw [show plane489GenSourceLb (361 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (361 : Fin 371) = [257, 129, 65, 32, 16, 9, 4, 3] by decide]
  exact space1634_lower

theorem plane489_source0362 : plane489GenConfig.sourceLb (362 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (362 : Fin 371)) := by
  change plane489GenSourceLb (362 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (362 : Fin 371)))
  rw [show plane489GenSourceLb (362 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (362 : Fin 371) = [256, 128, 65, 32, 17, 8, 5, 2] by decide]
  exact space1632_lower

theorem plane489_source0363 : plane489GenConfig.sourceLb (363 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (363 : Fin 371)) := by
  change plane489GenSourceLb (363 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (363 : Fin 371)))
  rw [show plane489GenSourceLb (363 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (363 : Fin 371) = [256, 129, 64, 33, 16, 8, 5, 2] by decide]
  exact space3391_lower

theorem plane489_source0364 : plane489GenConfig.sourceLb (364 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (364 : Fin 371)) := by
  change plane489GenSourceLb (364 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (364 : Fin 371)))
  rw [show plane489GenSourceLb (364 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (364 : Fin 371) = [256, 129, 64, 33, 17, 8, 4, 2] by decide]
  exact space1630_lower

theorem plane489_source0365 : plane489GenConfig.sourceLb (365 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (365 : Fin 371)) := by
  change plane489GenSourceLb (365 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (365 : Fin 371)))
  rw [show plane489GenSourceLb (365 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (365 : Fin 371) = [256, 129, 65, 33, 16, 8, 4, 2] by decide]
  exact space2022_lower

theorem plane489_source0366 : plane489GenConfig.sourceLb (366 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (366 : Fin 371)) := by
  change plane489GenSourceLb (366 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (366 : Fin 371)))
  rw [show plane489GenSourceLb (366 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (366 : Fin 371) = [258, 128, 64, 34, 18, 10, 6, 1] by decide]
  exact space1660_lower

theorem plane489_source0367 : plane489GenConfig.sourceLb (367 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (367 : Fin 371)) := by
  change plane489GenSourceLb (367 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (367 : Fin 371)))
  rw [show plane489GenSourceLb (367 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (367 : Fin 371) = [258, 130, 64, 34, 18, 10, 4, 1] by decide]
  exact space1662_lower

theorem plane489_source0368 : plane489GenConfig.sourceLb (368 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (368 : Fin 371)) := by
  change plane489GenSourceLb (368 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (368 : Fin 371)))
  rw [show plane489GenSourceLb (368 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (368 : Fin 371) = [258, 130, 66, 32, 18, 10, 4, 1] by decide]
  exact space1663_lower

theorem plane489_source0369 : plane489GenConfig.sourceLb (369 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (369 : Fin 371)) := by
  change plane489GenSourceLb (369 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (369 : Fin 371)))
  rw [show plane489GenSourceLb (369 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (369 : Fin 371) = [256, 128, 68, 36, 20, 8, 2, 1] by decide]
  exact space3392_lower

theorem plane489_source0370 : plane489GenConfig.sourceLb (370 : Fin 371) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (370 : Fin 371)) := by
  change plane489GenSourceLb (370 : Fin 371) ≤
    frozenWangTable.L0 (spanCodes (plane489GenSourceBasis (370 : Fin 371)))
  rw [show plane489GenSourceLb (370 : Fin 371) = 9 by decide,
      show plane489GenSourceBasis (370 : Fin 371) = [256, 132, 68, 32, 20, 8, 2, 1] by decide]
  exact space3393_lower

theorem plane489_sourceBlock011 (offset : Fin 32)
    (hlt : 11 * 32 + offset.val < 371) :
    plane489GenConfig.sourceLb (Fin.mk (11 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane489GenConfig.sourceU (Fin.mk (11 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane489_source0352
  | ⟨1, _⟩ => intro hlt; exact plane489_source0353
  | ⟨2, _⟩ => intro hlt; exact plane489_source0354
  | ⟨3, _⟩ => intro hlt; exact plane489_source0355
  | ⟨4, _⟩ => intro hlt; exact plane489_source0356
  | ⟨5, _⟩ => intro hlt; exact plane489_source0357
  | ⟨6, _⟩ => intro hlt; exact plane489_source0358
  | ⟨7, _⟩ => intro hlt; exact plane489_source0359
  | ⟨8, _⟩ => intro hlt; exact plane489_source0360
  | ⟨9, _⟩ => intro hlt; exact plane489_source0361
  | ⟨10, _⟩ => intro hlt; exact plane489_source0362
  | ⟨11, _⟩ => intro hlt; exact plane489_source0363
  | ⟨12, _⟩ => intro hlt; exact plane489_source0364
  | ⟨13, _⟩ => intro hlt; exact plane489_source0365
  | ⟨14, _⟩ => intro hlt; exact plane489_source0366
  | ⟨15, _⟩ => intro hlt; exact plane489_source0367
  | ⟨16, _⟩ => intro hlt; exact plane489_source0368
  | ⟨17, _⟩ => intro hlt; exact plane489_source0369
  | ⟨18, _⟩ => intro hlt; exact plane489_source0370
  | ⟨k + 19, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
