import QiushiPlane490GenData
import QiushiFrozenWangSpaces040
import QiushiFrozenWangSpaces041
import QiushiFrozenWangSpaces042
import QiushiFrozenWangSpaces046
import QiushiFrozenWangSpaces049
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces084
import QiushiFrozenWangSpaces085
import QiushiFrozenWangSpaces095
import QiushiFrozenWangSpaces096
import QiushiFrozenWangSpaces104
import QiushiFrozenWangSpaces119

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source0576 : plane490GenConfig.sourceLb (576 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (576 : Fin 713)) := by
  change plane490GenSourceLb (576 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (576 : Fin 713)))
  rw [show plane490GenSourceLb (576 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (576 : Fin 713) = [274, 146, 64, 32, 10, 6, 1] by decide]
  exact space3057_lower

theorem plane490_source0577 : plane490GenConfig.sourceLb (577 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (577 : Fin 713)) := by
  change plane490GenSourceLb (577 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (577 : Fin 713)))
  rw [show plane490GenSourceLb (577 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (577 : Fin 713) = [257, 128, 65, 35, 18, 10, 6] by decide]
  exact space3824_lower

theorem plane490_source0578 : plane490GenConfig.sourceLb (578 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (578 : Fin 713)) := by
  change plane490GenSourceLb (578 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (578 : Fin 713)))
  rw [show plane490GenSourceLb (578 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (578 : Fin 713) = [257, 129, 66, 33, 18, 10, 6] by decide]
  exact space2235_lower

theorem plane490_source0579 : plane490GenConfig.sourceLb (579 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (579 : Fin 713)) := by
  change plane490GenSourceLb (579 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (579 : Fin 713)))
  rw [show plane490GenSourceLb (579 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (579 : Fin 713) = [256, 128, 67, 32, 19, 10, 6] by decide]
  exact space1345_lower

theorem plane490_source0580 : plane490GenConfig.sourceLb (580 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (580 : Fin 713)) := by
  change plane490GenSourceLb (580 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (580 : Fin 713)))
  rw [show plane490GenSourceLb (580 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (580 : Fin 713) = [256, 130, 64, 33, 19, 10, 6] by decide]
  exact space1340_lower

theorem plane490_source0581 : plane490GenConfig.sourceLb (581 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (581 : Fin 713)) := by
  change plane490GenSourceLb (581 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (581 : Fin 713)))
  rw [show plane490GenSourceLb (581 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (581 : Fin 713) = [258, 131, 64, 34, 17, 10, 6] by decide]
  exact space3353_lower

theorem plane490_source0582 : plane490GenConfig.sourceLb (582 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (582 : Fin 713)) := by
  change plane490GenSourceLb (582 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (582 : Fin 713)))
  rw [show plane490GenSourceLb (582 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (582 : Fin 713) = [257, 130, 67, 34, 18, 10, 7] by decide]
  exact space3825_lower

theorem plane490_source0583 : plane490GenConfig.sourceLb (583 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (583 : Fin 713)) := by
  change plane490GenSourceLb (583 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (583 : Fin 713)))
  rw [show plane490GenSourceLb (583 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (583 : Fin 713) = [256, 129, 64, 35, 19, 10, 7] by decide]
  exact space1329_lower

theorem plane490_source0584 : plane490GenConfig.sourceLb (584 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (584 : Fin 713)) := by
  change plane490GenSourceLb (584 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (584 : Fin 713)))
  rw [show plane490GenSourceLb (584 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (584 : Fin 713) = [256, 128, 65, 35, 19, 10, 7] by decide]
  exact space1327_lower

theorem plane490_source0585 : plane490GenConfig.sourceLb (585 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (585 : Fin 713)) := by
  change plane490GenSourceLb (585 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (585 : Fin 713)))
  rw [show plane490GenSourceLb (585 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (585 : Fin 713) = [256, 128, 66, 32, 19, 10, 7] by decide]
  exact space1326_lower

theorem plane490_source0586 : plane490GenConfig.sourceLb (586 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (586 : Fin 713)) := by
  change plane490GenSourceLb (586 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (586 : Fin 713)))
  rw [show plane490GenSourceLb (586 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (586 : Fin 713) = [258, 130, 66, 32, 17, 10, 7] by decide]
  exact space2735_lower

theorem plane490_source0587 : plane490GenConfig.sourceLb (587 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (587 : Fin 713)) := by
  change plane490GenSourceLb (587 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (587 : Fin 713)))
  rw [show plane490GenSourceLb (587 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (587 : Fin 713) = [257, 130, 67, 33, 18, 10, 4] by decide]
  exact space3826_lower

theorem plane490_source0588 : plane490GenConfig.sourceLb (588 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (588 : Fin 713)) := by
  change plane490GenSourceLb (588 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (588 : Fin 713)))
  rw [show plane490GenSourceLb (588 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (588 : Fin 713) = [257, 128, 65, 33, 18, 10, 4] by decide]
  exact space3827_lower

theorem plane490_source0589 : plane490GenConfig.sourceLb (589 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (589 : Fin 713)) := by
  change plane490GenSourceLb (589 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (589 : Fin 713)))
  rw [show plane490GenSourceLb (589 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (589 : Fin 713) = [256, 128, 66, 35, 19, 10, 4] by decide]
  exact space1313_lower

theorem plane490_source0590 : plane490GenConfig.sourceLb (590 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (590 : Fin 713)) := by
  change plane490GenSourceLb (590 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (590 : Fin 713)))
  rw [show plane490GenSourceLb (590 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (590 : Fin 713) = [256, 131, 65, 35, 19, 10, 4] by decide]
  exact space1309_lower

theorem plane490_source0591 : plane490GenConfig.sourceLb (591 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (591 : Fin 713)) := by
  change plane490GenSourceLb (591 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (591 : Fin 713)))
  rw [show plane490GenSourceLb (591 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (591 : Fin 713) = [256, 129, 65, 33, 19, 10, 4] by decide]
  exact space1301_lower

theorem plane490_source0592 : plane490GenConfig.sourceLb (592 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (592 : Fin 713)) := by
  change plane490GenSourceLb (592 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (592 : Fin 713)))
  rw [show plane490GenSourceLb (592 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (592 : Fin 713) = [256, 131, 64, 35, 19, 10, 5] by decide]
  exact space1297_lower

theorem plane490_source0593 : plane490GenConfig.sourceLb (593 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (593 : Fin 713)) := by
  change plane490GenSourceLb (593 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (593 : Fin 713)))
  rw [show plane490GenSourceLb (593 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (593 : Fin 713) = [259, 128, 65, 34, 16, 10, 5] by decide]
  exact space2224_lower

theorem plane490_source0594 : plane490GenConfig.sourceLb (594 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (594 : Fin 713)) := by
  change plane490GenSourceLb (594 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (594 : Fin 713)))
  rw [show plane490GenSourceLb (594 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (594 : Fin 713) = [259, 130, 65, 32, 16, 10, 5] by decide]
  exact space2704_lower

theorem plane490_source0595 : plane490GenConfig.sourceLb (595 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (595 : Fin 713)) := by
  change plane490GenSourceLb (595 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (595 : Fin 713)))
  rw [show plane490GenSourceLb (595 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (595 : Fin 713) = [258, 129, 66, 33, 17, 10, 5] by decide]
  exact space3358_lower

theorem plane490_source0596 : plane490GenConfig.sourceLb (596 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (596 : Fin 713)) := by
  change plane490GenSourceLb (596 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (596 : Fin 713)))
  rw [show plane490GenSourceLb (596 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (596 : Fin 713) = [258, 130, 65, 33, 17, 10, 5] by decide]
  exact space3359_lower

theorem plane490_source0597 : plane490GenConfig.sourceLb (597 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (597 : Fin 713)) := by
  change plane490GenSourceLb (597 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (597 : Fin 713)))
  rw [show plane490GenSourceLb (597 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (597 : Fin 713) = [261, 133, 65, 36, 20, 8, 2] by decide]
  exact space3828_lower

theorem plane490_source0598 : plane490GenConfig.sourceLb (598 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (598 : Fin 713)) := by
  change plane490GenSourceLb (598 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (598 : Fin 713)))
  rw [show plane490GenSourceLb (598 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (598 : Fin 713) = [261, 128, 69, 37, 20, 8, 2] by decide]
  exact space3829_lower

theorem plane490_source0599 : plane490GenConfig.sourceLb (599 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (599 : Fin 713)) := by
  change plane490GenSourceLb (599 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (599 : Fin 713)))
  rw [show plane490GenSourceLb (599 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (599 : Fin 713) = [260, 132, 64, 37, 21, 8, 2] by decide]
  exact space3830_lower

theorem plane490_source0600 : plane490GenConfig.sourceLb (600 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (600 : Fin 713)) := by
  change plane490GenSourceLb (600 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (600 : Fin 713)))
  rw [show plane490GenSourceLb (600 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (600 : Fin 713) = [260, 132, 69, 32, 21, 8, 2] by decide]
  exact space3831_lower

theorem plane490_source0601 : plane490GenConfig.sourceLb (601 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (601 : Fin 713)) := by
  change plane490GenSourceLb (601 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (601 : Fin 713)))
  rw [show plane490GenSourceLb (601 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (601 : Fin 713) = [256, 133, 64, 32, 17, 8, 2] by decide]
  exact space1590_lower

theorem plane490_source0602 : plane490GenConfig.sourceLb (602 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (602 : Fin 713)) := by
  change plane490GenSourceLb (602 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (602 : Fin 713)))
  rw [show plane490GenSourceLb (602 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (602 : Fin 713) = [273, 144, 81, 49, 8, 4, 2] by decide]
  exact space3092_lower

theorem plane490_source0603 : plane490GenConfig.sourceLb (603 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (603 : Fin 713)) := by
  change plane490GenSourceLb (603 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (603 : Fin 713)))
  rw [show plane490GenSourceLb (603 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (603 : Fin 713) = [256, 128, 97, 17, 8, 4, 2] by decide]
  exact space1597_lower

theorem plane490_source0604 : plane490GenConfig.sourceLb (604 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (604 : Fin 713)) := by
  change plane490GenSourceLb (604 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (604 : Fin 713)))
  rw [show plane490GenSourceLb (604 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (604 : Fin 713) = [273, 145, 80, 48, 8, 5, 2] by decide]
  exact space3832_lower

theorem plane490_source0605 : plane490GenConfig.sourceLb (605 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (605 : Fin 713)) := by
  change plane490GenSourceLb (605 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (605 : Fin 713)))
  rw [show plane490GenSourceLb (605 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (605 : Fin 713) = [256, 193, 33, 17, 8, 5, 2] by decide]
  exact space1593_lower

theorem plane490_source0606 : plane490GenConfig.sourceLb (606 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (606 : Fin 713)) := by
  change plane490GenSourceLb (606 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (606 : Fin 713)))
  rw [show plane490GenSourceLb (606 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (606 : Fin 713) = [261, 133, 65, 36, 21, 9, 3] by decide]
  exact space3833_lower

theorem plane490_source0607 : plane490GenConfig.sourceLb (607 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (607 : Fin 713)) := by
  change plane490GenSourceLb (607 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (607 : Fin 713)))
  rw [show plane490GenSourceLb (607 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (607 : Fin 713) = [256, 128, 69, 32, 16, 9, 3] by decide]
  exact space1486_lower

theorem plane490_sourceBlock018 (offset : Fin 32)
    (hlt : 18 * 32 + offset.val < 713) :
    plane490GenConfig.sourceLb (Fin.mk (18 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (Fin.mk (18 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane490_source0576
  | ⟨1, _⟩ => intro hlt; exact plane490_source0577
  | ⟨2, _⟩ => intro hlt; exact plane490_source0578
  | ⟨3, _⟩ => intro hlt; exact plane490_source0579
  | ⟨4, _⟩ => intro hlt; exact plane490_source0580
  | ⟨5, _⟩ => intro hlt; exact plane490_source0581
  | ⟨6, _⟩ => intro hlt; exact plane490_source0582
  | ⟨7, _⟩ => intro hlt; exact plane490_source0583
  | ⟨8, _⟩ => intro hlt; exact plane490_source0584
  | ⟨9, _⟩ => intro hlt; exact plane490_source0585
  | ⟨10, _⟩ => intro hlt; exact plane490_source0586
  | ⟨11, _⟩ => intro hlt; exact plane490_source0587
  | ⟨12, _⟩ => intro hlt; exact plane490_source0588
  | ⟨13, _⟩ => intro hlt; exact plane490_source0589
  | ⟨14, _⟩ => intro hlt; exact plane490_source0590
  | ⟨15, _⟩ => intro hlt; exact plane490_source0591
  | ⟨16, _⟩ => intro hlt; exact plane490_source0592
  | ⟨17, _⟩ => intro hlt; exact plane490_source0593
  | ⟨18, _⟩ => intro hlt; exact plane490_source0594
  | ⟨19, _⟩ => intro hlt; exact plane490_source0595
  | ⟨20, _⟩ => intro hlt; exact plane490_source0596
  | ⟨21, _⟩ => intro hlt; exact plane490_source0597
  | ⟨22, _⟩ => intro hlt; exact plane490_source0598
  | ⟨23, _⟩ => intro hlt; exact plane490_source0599
  | ⟨24, _⟩ => intro hlt; exact plane490_source0600
  | ⟨25, _⟩ => intro hlt; exact plane490_source0601
  | ⟨26, _⟩ => intro hlt; exact plane490_source0602
  | ⟨27, _⟩ => intro hlt; exact plane490_source0603
  | ⟨28, _⟩ => intro hlt; exact plane490_source0604
  | ⟨29, _⟩ => intro hlt; exact plane490_source0605
  | ⟨30, _⟩ => intro hlt; exact plane490_source0606
  | ⟨31, _⟩ => intro hlt; exact plane490_source0607
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
