import QiushiPlane487GenData
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces063
import QiushiFrozenWangSpaces070
import QiushiFrozenWangSpaces087

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane487_source0640 : plane487GenConfig.sourceLb (640 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (640 : Fin 668)) := by
  change plane487GenSourceLb (640 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (640 : Fin 668)))
  rw [show plane487GenSourceLb (640 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (640 : Fin 668) = [256, 128, 66, 34, 18, 10, 4, 1] by decide]
  exact space1620_lower

theorem plane487_source0641 : plane487GenConfig.sourceLb (641 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (641 : Fin 668)) := by
  change plane487GenSourceLb (641 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (641 : Fin 668)))
  rw [show plane487GenSourceLb (641 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (641 : Fin 668) = [258, 128, 66, 32, 16, 10, 6, 1] by decide]
  exact space2791_lower

theorem plane487_source0642 : plane487GenConfig.sourceLb (642 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (642 : Fin 668)) := by
  change plane487GenSourceLb (642 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (642 : Fin 668)))
  rw [show plane487GenSourceLb (642 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (642 : Fin 668) = [256, 128, 66, 34, 16, 10, 6, 1] by decide]
  exact space2792_lower

theorem plane487_source0643 : plane487GenConfig.sourceLb (643 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (643 : Fin 668)) := by
  change plane487GenSourceLb (643 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (643 : Fin 668)))
  rw [show plane487GenSourceLb (643 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (643 : Fin 668) = [258, 128, 64, 34, 18, 10, 6, 1] by decide]
  exact space1660_lower

theorem plane487_source0644 : plane487GenConfig.sourceLb (644 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (644 : Fin 668)) := by
  change plane487GenSourceLb (644 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (644 : Fin 668)))
  rw [show plane487GenSourceLb (644 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (644 : Fin 668) = [256, 130, 64, 34, 18, 10, 6, 1] by decide]
  exact space1659_lower

theorem plane487_source0645 : plane487GenConfig.sourceLb (645 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (645 : Fin 668)) := by
  change plane487GenSourceLb (645 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (645 : Fin 668)))
  rw [show plane487GenSourceLb (645 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (645 : Fin 668) = [257, 128, 65, 32, 17, 8, 4, 2] by decide]
  exact space1628_lower

theorem plane487_source0646 : plane487GenConfig.sourceLb (646 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (646 : Fin 668)) := by
  change plane487GenSourceLb (646 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (646 : Fin 668)))
  rw [show plane487GenSourceLb (646 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (646 : Fin 668) = [257, 129, 64, 32, 17, 8, 5, 2] by decide]
  exact space1654_lower

theorem plane487_source0647 : plane487GenConfig.sourceLb (647 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (647 : Fin 668)) := by
  change plane487GenSourceLb (647 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (647 : Fin 668)))
  rw [show plane487GenSourceLb (647 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (647 : Fin 668) = [257, 128, 64, 33, 17, 8, 5, 2] by decide]
  exact space1652_lower

theorem plane487_source0648 : plane487GenConfig.sourceLb (648 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (648 : Fin 668)) := by
  change plane487GenSourceLb (648 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (648 : Fin 668)))
  rw [show plane487GenSourceLb (648 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (648 : Fin 668) = [256, 129, 64, 33, 17, 8, 5, 2] by decide]
  exact space1651_lower

theorem plane487_source0649 : plane487GenConfig.sourceLb (649 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (649 : Fin 668)) := by
  change plane487GenSourceLb (649 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (649 : Fin 668)))
  rw [show plane487GenSourceLb (649 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (649 : Fin 668) = [257, 128, 64, 32, 16, 9, 4, 3] by decide]
  exact space1633_lower

theorem plane487_source0650 : plane487GenConfig.sourceLb (650 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (650 : Fin 668)) := by
  change plane487GenSourceLb (650 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (650 : Fin 668)))
  rw [show plane487GenSourceLb (650 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (650 : Fin 668) = [257, 128, 65, 33, 17, 9, 4, 3] by decide]
  exact space2793_lower

theorem plane487_source0651 : plane487GenConfig.sourceLb (651 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (651 : Fin 668)) := by
  change plane487GenSourceLb (651 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (651 : Fin 668)))
  rw [show plane487GenSourceLb (651 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (651 : Fin 668) = [256, 129, 65, 33, 16, 9, 5, 3] by decide]
  exact space1639_lower

theorem plane487_source0652 : plane487GenConfig.sourceLb (652 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (652 : Fin 668)) := by
  change plane487GenSourceLb (652 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (652 : Fin 668)))
  rw [show plane487GenSourceLb (652 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (652 : Fin 668) = [256, 129, 64, 32, 17, 9, 5, 3] by decide]
  exact space2021_lower

theorem plane487_source0653 : plane487GenConfig.sourceLb (653 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (653 : Fin 668)) := by
  change plane487GenSourceLb (653 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (653 : Fin 668)))
  rw [show plane487GenSourceLb (653 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (653 : Fin 668) = [257, 129, 64, 32, 17, 9, 5, 3] by decide]
  exact space2018_lower

theorem plane487_source0654 : plane487GenConfig.sourceLb (654 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (654 : Fin 668)) := by
  change plane487GenSourceLb (654 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (654 : Fin 668)))
  rw [show plane487GenSourceLb (654 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (654 : Fin 668) = [256, 128, 65, 33, 16, 9, 5, 3] by decide]
  exact space1638_lower

theorem plane487_source0655 : plane487GenConfig.sourceLb (655 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (655 : Fin 668)) := by
  change plane487GenSourceLb (655 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (655 : Fin 668)))
  rw [show plane487GenSourceLb (655 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (655 : Fin 668) = [256, 129, 65, 32, 16, 9, 5, 3] by decide]
  exact space1636_lower

theorem plane487_source0656 : plane487GenConfig.sourceLb (656 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (656 : Fin 668)) := by
  change plane487GenSourceLb (656 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (656 : Fin 668)))
  rw [show plane487GenSourceLb (656 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (656 : Fin 668) = [257, 128, 65, 32, 16, 9, 5, 3] by decide]
  exact space1635_lower

theorem plane487_source0657 : plane487GenConfig.sourceLb (657 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (657 : Fin 668)) := by
  change plane487GenSourceLb (657 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (657 : Fin 668)))
  rw [show plane487GenSourceLb (657 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (657 : Fin 668) = [256, 129, 64, 33, 16, 9, 4, 3] by decide]
  exact space1645_lower

theorem plane487_source0658 : plane487GenConfig.sourceLb (658 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (658 : Fin 668)) := by
  change plane487GenSourceLb (658 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (658 : Fin 668)))
  rw [show plane487GenSourceLb (658 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (658 : Fin 668) = [257, 128, 64, 33, 16, 9, 4, 3] by decide]
  exact space1646_lower

theorem plane487_source0659 : plane487GenConfig.sourceLb (659 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (659 : Fin 668)) := by
  change plane487GenSourceLb (659 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (659 : Fin 668)))
  rw [show plane487GenSourceLb (659 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (659 : Fin 668) = [257, 129, 64, 32, 16, 9, 4, 3] by decide]
  exact space1648_lower

theorem plane487_source0660 : plane487GenConfig.sourceLb (660 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (660 : Fin 668)) := by
  change plane487GenSourceLb (660 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (660 : Fin 668)))
  rw [show plane487GenSourceLb (660 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (660 : Fin 668) = [257, 128, 64, 32, 17, 8, 5, 2] by decide]
  exact space1631_lower

theorem plane487_source0661 : plane487GenConfig.sourceLb (661 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (661 : Fin 668)) := by
  change plane487GenSourceLb (661 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (661 : Fin 668)))
  rw [show plane487GenSourceLb (661 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (661 : Fin 668) = [256, 129, 65, 33, 16, 8, 5, 2] by decide]
  exact space2251_lower

theorem plane487_source0662 : plane487GenConfig.sourceLb (662 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (662 : Fin 668)) := by
  change plane487GenSourceLb (662 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (662 : Fin 668)))
  rw [show plane487GenSourceLb (662 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (662 : Fin 668) = [256, 129, 65, 33, 17, 8, 4, 2] by decide]
  exact space1655_lower

theorem plane487_source0663 : plane487GenConfig.sourceLb (663 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (663 : Fin 668)) := by
  change plane487GenSourceLb (663 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (663 : Fin 668)))
  rw [show plane487GenSourceLb (663 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (663 : Fin 668) = [257, 129, 65, 32, 17, 8, 4, 2] by decide]
  exact space1657_lower

theorem plane487_source0664 : plane487GenConfig.sourceLb (664 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (664 : Fin 668)) := by
  change plane487GenSourceLb (664 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (664 : Fin 668)))
  rw [show plane487GenSourceLb (664 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (664 : Fin 668) = [257, 129, 64, 33, 16, 8, 4, 2] by decide]
  exact space2023_lower

theorem plane487_source0665 : plane487GenConfig.sourceLb (665 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (665 : Fin 668)) := by
  change plane487GenSourceLb (665 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (665 : Fin 668)))
  rw [show plane487GenSourceLb (665 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (665 : Fin 668) = [258, 128, 64, 32, 18, 10, 6, 1] by decide]
  exact space1621_lower

theorem plane487_source0666 : plane487GenConfig.sourceLb (666 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (666 : Fin 668)) := by
  change plane487GenSourceLb (666 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (666 : Fin 668)))
  rw [show plane487GenSourceLb (666 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (666 : Fin 668) = [256, 130, 66, 34, 18, 10, 4, 1] by decide]
  exact space1661_lower

theorem plane487_source0667 : plane487GenConfig.sourceLb (667 : Fin 668) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (667 : Fin 668)) := by
  change plane487GenSourceLb (667 : Fin 668) ≤
    frozenWangTable.L0 (spanCodes (plane487GenSourceBasis (667 : Fin 668)))
  rw [show plane487GenSourceLb (667 : Fin 668) = 9 by decide,
      show plane487GenSourceBasis (667 : Fin 668) = [258, 130, 64, 34, 16, 10, 4, 1] by decide]
  exact space2024_lower

theorem plane487_sourceBlock020 (offset : Fin 32)
    (hlt : 20 * 32 + offset.val < 668) :
    plane487GenConfig.sourceLb (Fin.mk (20 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane487GenConfig.sourceU (Fin.mk (20 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane487_source0640
  | ⟨1, _⟩ => intro hlt; exact plane487_source0641
  | ⟨2, _⟩ => intro hlt; exact plane487_source0642
  | ⟨3, _⟩ => intro hlt; exact plane487_source0643
  | ⟨4, _⟩ => intro hlt; exact plane487_source0644
  | ⟨5, _⟩ => intro hlt; exact plane487_source0645
  | ⟨6, _⟩ => intro hlt; exact plane487_source0646
  | ⟨7, _⟩ => intro hlt; exact plane487_source0647
  | ⟨8, _⟩ => intro hlt; exact plane487_source0648
  | ⟨9, _⟩ => intro hlt; exact plane487_source0649
  | ⟨10, _⟩ => intro hlt; exact plane487_source0650
  | ⟨11, _⟩ => intro hlt; exact plane487_source0651
  | ⟨12, _⟩ => intro hlt; exact plane487_source0652
  | ⟨13, _⟩ => intro hlt; exact plane487_source0653
  | ⟨14, _⟩ => intro hlt; exact plane487_source0654
  | ⟨15, _⟩ => intro hlt; exact plane487_source0655
  | ⟨16, _⟩ => intro hlt; exact plane487_source0656
  | ⟨17, _⟩ => intro hlt; exact plane487_source0657
  | ⟨18, _⟩ => intro hlt; exact plane487_source0658
  | ⟨19, _⟩ => intro hlt; exact plane487_source0659
  | ⟨20, _⟩ => intro hlt; exact plane487_source0660
  | ⟨21, _⟩ => intro hlt; exact plane487_source0661
  | ⟨22, _⟩ => intro hlt; exact plane487_source0662
  | ⟨23, _⟩ => intro hlt; exact plane487_source0663
  | ⟨24, _⟩ => intro hlt; exact plane487_source0664
  | ⟨25, _⟩ => intro hlt; exact plane487_source0665
  | ⟨26, _⟩ => intro hlt; exact plane487_source0666
  | ⟨27, _⟩ => intro hlt; exact plane487_source0667
  | ⟨k + 28, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
