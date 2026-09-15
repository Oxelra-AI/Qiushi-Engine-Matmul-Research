import QiushiPlane490GenData
import QiushiFrozenWangSpaces036
import QiushiFrozenWangSpaces048
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces070
import QiushiFrozenWangSpaces095
import QiushiFrozenWangSpaces118
import QiushiFrozenWangSpaces119

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source0512 : plane490GenConfig.sourceLb (512 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (512 : Fin 713)) := by
  change plane490GenSourceLb (512 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (512 : Fin 713)))
  rw [show plane490GenSourceLb (512 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (512 : Fin 713) = [260, 132, 64, 32, 20, 9, 3] by decide]
  exact space3801_lower

theorem plane490_source0513 : plane490GenConfig.sourceLb (513 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (513 : Fin 713)) := by
  change plane490GenSourceLb (513 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (513 : Fin 713)))
  rw [show plane490GenSourceLb (513 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (513 : Fin 713) = [256, 129, 64, 33, 17, 8, 2] by decide]
  exact space1176_lower

theorem plane490_source0514 : plane490GenConfig.sourceLb (514 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (514 : Fin 713)) := by
  change plane490GenSourceLb (514 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (514 : Fin 713)))
  rw [show plane490GenSourceLb (514 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (514 : Fin 713) = [256, 132, 64, 36, 17, 8, 2] by decide]
  exact space3802_lower

theorem plane490_source0515 : plane490GenConfig.sourceLb (515 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (515 : Fin 713)) := by
  change plane490GenSourceLb (515 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (515 : Fin 713)))
  rw [show plane490GenSourceLb (515 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (515 : Fin 713) = [256, 128, 68, 36, 17, 8, 2] by decide]
  exact space3803_lower

theorem plane490_source0516 : plane490GenConfig.sourceLb (516 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (516 : Fin 713)) := by
  change plane490GenSourceLb (516 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (516 : Fin 713)))
  rw [show plane490GenSourceLb (516 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (516 : Fin 713) = [257, 129, 65, 33, 16, 8, 2] by decide]
  exact space3804_lower

theorem plane490_source0517 : plane490GenConfig.sourceLb (517 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (517 : Fin 713)) := by
  change plane490GenSourceLb (517 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (517 : Fin 713)))
  rw [show plane490GenSourceLb (517 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (517 : Fin 713) = [260, 133, 68, 37, 21, 8, 2] by decide]
  exact space2222_lower

theorem plane490_source0518 : plane490GenConfig.sourceLb (518 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (518 : Fin 713)) := by
  change plane490GenSourceLb (518 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (518 : Fin 713)))
  rw [show plane490GenSourceLb (518 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (518 : Fin 713) = [256, 134, 68, 34, 18, 10, 1] by decide]
  exact space1168_lower

theorem plane490_source0519 : plane490GenConfig.sourceLb (519 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (519 : Fin 713)) := by
  change plane490GenSourceLb (519 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (519 : Fin 713)))
  rw [show plane490GenSourceLb (519 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (519 : Fin 713) = [256, 134, 70, 32, 18, 10, 1] by decide]
  exact space1166_lower

theorem plane490_source0520 : plane490GenConfig.sourceLb (520 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (520 : Fin 713)) := by
  change plane490GenSourceLb (520 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (520 : Fin 713)))
  rw [show plane490GenSourceLb (520 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (520 : Fin 713) = [256, 132, 68, 32, 18, 10, 1] by decide]
  exact space1164_lower

theorem plane490_source0521 : plane490GenConfig.sourceLb (521 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (521 : Fin 713)) := by
  change plane490GenSourceLb (521 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (521 : Fin 713)))
  rw [show plane490GenSourceLb (521 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (521 : Fin 713) = [256, 130, 68, 38, 18, 10, 1] by decide]
  exact space1172_lower

theorem plane490_source0522 : plane490GenConfig.sourceLb (522 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (522 : Fin 713)) := by
  change plane490GenSourceLb (522 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (522 : Fin 713)))
  rw [show plane490GenSourceLb (522 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (522 : Fin 713) = [256, 128, 68, 36, 18, 10, 1] by decide]
  exact space1170_lower

theorem plane490_source0523 : plane490GenConfig.sourceLb (523 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (523 : Fin 713)) := by
  change plane490GenSourceLb (523 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (523 : Fin 713)))
  rw [show plane490GenSourceLb (523 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (523 : Fin 713) = [259, 130, 65, 35, 16, 10, 4] by decide]
  exact space3805_lower

theorem plane490_source0524 : plane490GenConfig.sourceLb (524 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (524 : Fin 713)) := by
  change plane490GenSourceLb (524 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (524 : Fin 713)))
  rw [show plane490GenSourceLb (524 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (524 : Fin 713) = [257, 129, 66, 33, 18, 10, 4] by decide]
  exact space3806_lower

theorem plane490_source0525 : plane490GenConfig.sourceLb (525 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (525 : Fin 713)) := by
  change plane490GenSourceLb (525 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (525 : Fin 713)))
  rw [show plane490GenSourceLb (525 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (525 : Fin 713) = [257, 129, 65, 34, 18, 10, 4] by decide]
  exact space3807_lower

theorem plane490_source0526 : plane490GenConfig.sourceLb (526 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (526 : Fin 713)) := by
  change plane490GenSourceLb (526 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (526 : Fin 713)))
  rw [show plane490GenSourceLb (526 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (526 : Fin 713) = [257, 128, 65, 35, 18, 10, 4] by decide]
  exact space3808_lower

theorem plane490_source0527 : plane490GenConfig.sourceLb (527 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (527 : Fin 713)) := by
  change plane490GenSourceLb (527 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (527 : Fin 713)))
  rw [show plane490GenSourceLb (527 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (527 : Fin 713) = [256, 130, 64, 33, 19, 10, 4] by decide]
  exact space1564_lower

theorem plane490_source0528 : plane490GenConfig.sourceLb (528 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (528 : Fin 713)) := by
  change plane490GenSourceLb (528 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (528 : Fin 713)))
  rw [show plane490GenSourceLb (528 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (528 : Fin 713) = [256, 128, 66, 33, 19, 10, 4] by decide]
  exact space1562_lower

theorem plane490_source0529 : plane490GenConfig.sourceLb (529 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (529 : Fin 713)) := by
  change plane490GenSourceLb (529 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (529 : Fin 713)))
  rw [show plane490GenSourceLb (529 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (529 : Fin 713) = [256, 129, 65, 35, 19, 10, 4] by decide]
  exact space1554_lower

theorem plane490_source0530 : plane490GenConfig.sourceLb (530 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (530 : Fin 713)) := by
  change plane490GenSourceLb (530 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (530 : Fin 713)))
  rw [show plane490GenSourceLb (530 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (530 : Fin 713) = [256, 130, 66, 35, 19, 10, 4] by decide]
  exact space1552_lower

theorem plane490_source0531 : plane490GenConfig.sourceLb (531 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (531 : Fin 713)) := by
  change plane490GenSourceLb (531 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (531 : Fin 713)))
  rw [show plane490GenSourceLb (531 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (531 : Fin 713) = [259, 130, 65, 34, 16, 10, 5] by decide]
  exact space2242_lower

theorem plane490_source0532 : plane490GenConfig.sourceLb (532 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (532 : Fin 713)) := by
  change plane490GenSourceLb (532 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (532 : Fin 713)))
  rw [show plane490GenSourceLb (532 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (532 : Fin 713) = [257, 131, 64, 32, 18, 10, 5] by decide]
  exact space3066_lower

theorem plane490_source0533 : plane490GenConfig.sourceLb (533 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (533 : Fin 713)) := by
  change plane490GenSourceLb (533 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (533 : Fin 713)))
  rw [show plane490GenSourceLb (533 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (533 : Fin 713) = [257, 129, 66, 32, 18, 10, 5] by decide]
  exact space3809_lower

theorem plane490_source0534 : plane490GenConfig.sourceLb (534 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (534 : Fin 713)) := by
  change plane490GenSourceLb (534 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (534 : Fin 713)))
  rw [show plane490GenSourceLb (534 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (534 : Fin 713) = [257, 130, 64, 33, 18, 10, 5] by decide]
  exact space3810_lower

theorem plane490_source0535 : plane490GenConfig.sourceLb (535 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (535 : Fin 713)) := by
  change plane490GenSourceLb (535 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (535 : Fin 713)))
  rw [show plane490GenSourceLb (535 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (535 : Fin 713) = [257, 131, 65, 33, 18, 10, 5] by decide]
  exact space3811_lower

theorem plane490_source0536 : plane490GenConfig.sourceLb (536 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (536 : Fin 713)) := by
  change plane490GenSourceLb (536 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (536 : Fin 713)))
  rw [show plane490GenSourceLb (536 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (536 : Fin 713) = [257, 131, 66, 34, 18, 10, 5] by decide]
  exact space3812_lower

theorem plane490_source0537 : plane490GenConfig.sourceLb (537 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (537 : Fin 713)) := by
  change plane490GenSourceLb (537 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (537 : Fin 713)))
  rw [show plane490GenSourceLb (537 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (537 : Fin 713) = [256, 130, 64, 32, 19, 10, 5] by decide]
  exact space1550_lower

theorem plane490_source0538 : plane490GenConfig.sourceLb (538 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (538 : Fin 713)) := by
  change plane490GenSourceLb (538 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (538 : Fin 713)))
  rw [show plane490GenSourceLb (538 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (538 : Fin 713) = [256, 131, 65, 32, 19, 10, 5] by decide]
  exact space1548_lower

theorem plane490_source0539 : plane490GenConfig.sourceLb (539 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (539 : Fin 713)) := by
  change plane490GenSourceLb (539 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (539 : Fin 713)))
  rw [show plane490GenSourceLb (539 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (539 : Fin 713) = [256, 128, 67, 33, 19, 10, 5] by decide]
  exact space1541_lower

theorem plane490_source0540 : plane490GenConfig.sourceLb (540 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (540 : Fin 713)) := by
  change plane490GenSourceLb (540 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (540 : Fin 713)))
  rw [show plane490GenSourceLb (540 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (540 : Fin 713) = [256, 128, 65, 35, 19, 10, 5] by decide]
  exact space1540_lower

theorem plane490_source0541 : plane490GenConfig.sourceLb (541 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (541 : Fin 713)) := by
  change plane490GenSourceLb (541 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (541 : Fin 713)))
  rw [show plane490GenSourceLb (541 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (541 : Fin 713) = [258, 130, 66, 35, 17, 10, 6] by decide]
  exact space3813_lower

theorem plane490_source0542 : plane490GenConfig.sourceLb (542 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (542 : Fin 713)) := by
  change plane490GenSourceLb (542 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (542 : Fin 713)))
  rw [show plane490GenSourceLb (542 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (542 : Fin 713) = [257, 128, 65, 33, 18, 10, 6] by decide]
  exact space1997_lower

theorem plane490_source0543 : plane490GenConfig.sourceLb (543 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (543 : Fin 713)) := by
  change plane490GenSourceLb (543 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (543 : Fin 713)))
  rw [show plane490GenSourceLb (543 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (543 : Fin 713) = [257, 130, 65, 35, 18, 10, 6] by decide]
  exact space3814_lower

theorem plane490_sourceBlock016 (offset : Fin 32)
    (hlt : 16 * 32 + offset.val < 713) :
    plane490GenConfig.sourceLb (Fin.mk (16 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (Fin.mk (16 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane490_source0512
  | ⟨1, _⟩ => intro hlt; exact plane490_source0513
  | ⟨2, _⟩ => intro hlt; exact plane490_source0514
  | ⟨3, _⟩ => intro hlt; exact plane490_source0515
  | ⟨4, _⟩ => intro hlt; exact plane490_source0516
  | ⟨5, _⟩ => intro hlt; exact plane490_source0517
  | ⟨6, _⟩ => intro hlt; exact plane490_source0518
  | ⟨7, _⟩ => intro hlt; exact plane490_source0519
  | ⟨8, _⟩ => intro hlt; exact plane490_source0520
  | ⟨9, _⟩ => intro hlt; exact plane490_source0521
  | ⟨10, _⟩ => intro hlt; exact plane490_source0522
  | ⟨11, _⟩ => intro hlt; exact plane490_source0523
  | ⟨12, _⟩ => intro hlt; exact plane490_source0524
  | ⟨13, _⟩ => intro hlt; exact plane490_source0525
  | ⟨14, _⟩ => intro hlt; exact plane490_source0526
  | ⟨15, _⟩ => intro hlt; exact plane490_source0527
  | ⟨16, _⟩ => intro hlt; exact plane490_source0528
  | ⟨17, _⟩ => intro hlt; exact plane490_source0529
  | ⟨18, _⟩ => intro hlt; exact plane490_source0530
  | ⟨19, _⟩ => intro hlt; exact plane490_source0531
  | ⟨20, _⟩ => intro hlt; exact plane490_source0532
  | ⟨21, _⟩ => intro hlt; exact plane490_source0533
  | ⟨22, _⟩ => intro hlt; exact plane490_source0534
  | ⟨23, _⟩ => intro hlt; exact plane490_source0535
  | ⟨24, _⟩ => intro hlt; exact plane490_source0536
  | ⟨25, _⟩ => intro hlt; exact plane490_source0537
  | ⟨26, _⟩ => intro hlt; exact plane490_source0538
  | ⟨27, _⟩ => intro hlt; exact plane490_source0539
  | ⟨28, _⟩ => intro hlt; exact plane490_source0540
  | ⟨29, _⟩ => intro hlt; exact plane490_source0541
  | ⟨30, _⟩ => intro hlt; exact plane490_source0542
  | ⟨31, _⟩ => intro hlt; exact plane490_source0543
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
