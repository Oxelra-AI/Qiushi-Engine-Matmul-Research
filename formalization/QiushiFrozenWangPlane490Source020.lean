import QiushiPlane490GenData
import QiushiFrozenWangSpaces045
import QiushiFrozenWangSpaces046
import QiushiFrozenWangSpaces049
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces084
import QiushiFrozenWangSpaces086
import QiushiFrozenWangSpaces120

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source0640 : plane490GenConfig.sourceLb (640 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (640 : Fin 713)) := by
  change plane490GenSourceLb (640 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (640 : Fin 713)))
  rw [show plane490GenSourceLb (640 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (640 : Fin 713) = [257, 130, 64, 35, 18, 10, 4] by decide]
  exact space2237_lower

theorem plane490_source0641 : plane490GenConfig.sourceLb (641 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (641 : Fin 713)) := by
  change plane490GenSourceLb (641 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (641 : Fin 713)))
  rw [show plane490GenSourceLb (641 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (641 : Fin 713) = [257, 131, 64, 34, 18, 10, 4] by decide]
  exact space2236_lower

theorem plane490_source0642 : plane490GenConfig.sourceLb (642 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (642 : Fin 713)) := by
  change plane490GenSourceLb (642 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (642 : Fin 713)))
  rw [show plane490GenSourceLb (642 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (642 : Fin 713) = [257, 129, 65, 33, 18, 10, 4] by decide]
  exact space3850_lower

theorem plane490_source0643 : plane490GenConfig.sourceLb (643 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (643 : Fin 713)) := by
  change plane490GenSourceLb (643 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (643 : Fin 713)))
  rw [show plane490GenSourceLb (643 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (643 : Fin 713) = [259, 131, 67, 35, 16, 10, 4] by decide]
  exact space3851_lower

theorem plane490_source0644 : plane490GenConfig.sourceLb (644 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (644 : Fin 713)) := by
  change plane490GenSourceLb (644 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (644 : Fin 713)))
  rw [show plane490GenSourceLb (644 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (644 : Fin 713) = [261, 128, 68, 37, 21, 9, 3] by decide]
  exact space3852_lower

theorem plane490_source0645 : plane490GenConfig.sourceLb (645 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (645 : Fin 713)) := by
  change plane490GenSourceLb (645 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (645 : Fin 713)))
  rw [show plane490GenSourceLb (645 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (645 : Fin 713) = [261, 128, 65, 32, 21, 9, 3] by decide]
  exact space2696_lower

theorem plane490_source0646 : plane490GenConfig.sourceLb (646 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (646 : Fin 713)) := by
  change plane490GenSourceLb (646 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (646 : Fin 713)))
  rw [show plane490GenSourceLb (646 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (646 : Fin 713) = [260, 132, 65, 37, 20, 9, 3] by decide]
  exact space3853_lower

theorem plane490_source0647 : plane490GenConfig.sourceLb (647 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (647 : Fin 713)) := by
  change plane490GenSourceLb (647 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (647 : Fin 713)))
  rw [show plane490GenSourceLb (647 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (647 : Fin 713) = [260, 129, 69, 36, 20, 9, 3] by decide]
  exact space3854_lower

theorem plane490_source0648 : plane490GenConfig.sourceLb (648 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (648 : Fin 713)) := by
  change plane490GenSourceLb (648 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (648 : Fin 713)))
  rw [show plane490GenSourceLb (648 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (648 : Fin 713) = [260, 128, 68, 36, 20, 9, 3] by decide]
  exact space3855_lower

theorem plane490_source0649 : plane490GenConfig.sourceLb (649 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (649 : Fin 713)) := by
  change plane490GenSourceLb (649 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (649 : Fin 713)))
  rw [show plane490GenSourceLb (649 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (649 : Fin 713) = [260, 133, 65, 36, 20, 9, 3] by decide]
  exact space2003_lower

theorem plane490_source0650 : plane490GenConfig.sourceLb (650 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (650 : Fin 713)) := by
  change plane490GenSourceLb (650 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (650 : Fin 713)))
  rw [show plane490GenSourceLb (650 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (650 : Fin 713) = [260, 129, 64, 33, 20, 9, 3] by decide]
  exact space3856_lower

theorem plane490_source0651 : plane490GenConfig.sourceLb (651 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (651 : Fin 713)) := by
  change plane490GenSourceLb (651 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (651 : Fin 713)))
  rw [show plane490GenSourceLb (651 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (651 : Fin 713) = [260, 132, 68, 32, 20, 9, 3] by decide]
  exact space3857_lower

theorem plane490_source0652 : plane490GenConfig.sourceLb (652 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (652 : Fin 713)) := by
  change plane490GenSourceLb (652 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (652 : Fin 713)))
  rw [show plane490GenSourceLb (652 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (652 : Fin 713) = [256, 129, 64, 37, 16, 9, 3] by decide]
  exact space3858_lower

theorem plane490_source0653 : plane490GenConfig.sourceLb (653 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (653 : Fin 713)) := by
  change plane490GenSourceLb (653 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (653 : Fin 713)))
  rw [show plane490GenSourceLb (653 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (653 : Fin 713) = [256, 128, 68, 32, 16, 9, 3] by decide]
  exact space1571_lower

theorem plane490_source0654 : plane490GenConfig.sourceLb (654 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (654 : Fin 713)) := by
  change plane490GenSourceLb (654 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (654 : Fin 713)))
  rw [show plane490GenSourceLb (654 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (654 : Fin 713) = [256, 132, 64, 32, 16, 9, 3] by decide]
  exact space3859_lower

theorem plane490_source0655 : plane490GenConfig.sourceLb (655 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (655 : Fin 713)) := by
  change plane490GenSourceLb (655 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (655 : Fin 713)))
  rw [show plane490GenSourceLb (655 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (655 : Fin 713) = [272, 144, 80, 49, 9, 5, 3] by decide]
  exact space3860_lower

theorem plane490_source0656 : plane490GenConfig.sourceLb (656 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (656 : Fin 713)) := by
  change plane490GenSourceLb (656 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (656 : Fin 713)))
  rw [show plane490GenSourceLb (656 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (656 : Fin 713) = [272, 129, 64, 48, 9, 5, 3] by decide]
  exact space3861_lower

theorem plane490_source0657 : plane490GenConfig.sourceLb (657 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (657 : Fin 713)) := by
  change plane490GenSourceLb (657 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (657 : Fin 713)))
  rw [show plane490GenSourceLb (657 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (657 : Fin 713) = [272, 128, 81, 32, 9, 5, 3] by decide]
  exact space2758_lower

theorem plane490_source0658 : plane490GenConfig.sourceLb (658 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (658 : Fin 713)) := by
  change plane490GenSourceLb (658 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (658 : Fin 713)))
  rw [show plane490GenSourceLb (658 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (658 : Fin 713) = [272, 144, 65, 33, 9, 4, 3] by decide]
  exact space3862_lower

theorem plane490_source0659 : plane490GenConfig.sourceLb (659 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (659 : Fin 713)) := by
  change plane490GenSourceLb (659 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (659 : Fin 713)))
  rw [show plane490GenSourceLb (659 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (659 : Fin 713) = [256, 193, 33, 16, 9, 4, 3] by decide]
  exact space3863_lower

theorem plane490_source0660 : plane490GenConfig.sourceLb (660 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (660 : Fin 713)) := by
  change plane490GenSourceLb (660 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (660 : Fin 713)))
  rw [show plane490GenSourceLb (660 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (660 : Fin 713) = [260, 128, 68, 36, 21, 8, 2] by decide]
  exact space3864_lower

theorem plane490_source0661 : plane490GenConfig.sourceLb (661 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (661 : Fin 713)) := by
  change plane490GenSourceLb (661 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (661 : Fin 713)))
  rw [show plane490GenSourceLb (661 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (661 : Fin 713) = [260, 132, 68, 32, 21, 8, 2] by decide]
  exact space3865_lower

theorem plane490_source0662 : plane490GenConfig.sourceLb (662 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (662 : Fin 713)) := by
  change plane490GenSourceLb (662 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (662 : Fin 713)))
  rw [show plane490GenSourceLb (662 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (662 : Fin 713) = [260, 129, 65, 32, 21, 8, 2] by decide]
  exact space2691_lower

theorem plane490_source0663 : plane490GenConfig.sourceLb (663 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (663 : Fin 713)) := by
  change plane490GenSourceLb (663 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (663 : Fin 713)))
  rw [show plane490GenSourceLb (663 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (663 : Fin 713) = [261, 129, 68, 36, 20, 8, 2] by decide]
  exact space3866_lower

theorem plane490_source0664 : plane490GenConfig.sourceLb (664 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (664 : Fin 713)) := by
  change plane490GenSourceLb (664 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (664 : Fin 713)))
  rw [show plane490GenSourceLb (664 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (664 : Fin 713) = [261, 133, 64, 36, 20, 8, 2] by decide]
  exact space1984_lower

theorem plane490_source0665 : plane490GenConfig.sourceLb (665 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (665 : Fin 713)) := by
  change plane490GenSourceLb (665 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (665 : Fin 713)))
  rw [show plane490GenSourceLb (665 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (665 : Fin 713) = [256, 133, 69, 36, 17, 8, 2] by decide]
  exact space1459_lower

theorem plane490_source0666 : plane490GenConfig.sourceLb (666 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (666 : Fin 713)) := by
  change plane490GenSourceLb (666 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (666 : Fin 713)))
  rw [show plane490GenSourceLb (666 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (666 : Fin 713) = [256, 132, 68, 36, 17, 8, 2] by decide]
  exact space1458_lower

theorem plane490_source0667 : plane490GenConfig.sourceLb (667 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (667 : Fin 713)) := by
  change plane490GenSourceLb (667 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (667 : Fin 713)))
  rw [show plane490GenSourceLb (667 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (667 : Fin 713) = [256, 132, 65, 33, 17, 8, 2] by decide]
  exact space1470_lower

theorem plane490_source0668 : plane490GenConfig.sourceLb (668 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (668 : Fin 713)) := by
  change plane490GenSourceLb (668 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (668 : Fin 713)))
  rw [show plane490GenSourceLb (668 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (668 : Fin 713) = [256, 132, 64, 32, 17, 8, 2] by decide]
  exact space1467_lower

theorem plane490_source0669 : plane490GenConfig.sourceLb (669 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (669 : Fin 713)) := by
  change plane490GenSourceLb (669 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (669 : Fin 713)))
  rw [show plane490GenSourceLb (669 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (669 : Fin 713) = [257, 133, 65, 33, 16, 8, 2] by decide]
  exact space3867_lower

theorem plane490_source0670 : plane490GenConfig.sourceLb (670 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (670 : Fin 713)) := by
  change plane490GenSourceLb (670 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (670 : Fin 713)))
  rw [show plane490GenSourceLb (670 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (670 : Fin 713) = [273, 128, 81, 33, 8, 5, 2] by decide]
  exact space2779_lower

theorem plane490_source0671 : plane490GenConfig.sourceLb (671 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (671 : Fin 713)) := by
  change plane490GenSourceLb (671 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (671 : Fin 713)))
  rw [show plane490GenSourceLb (671 : Fin 713) = 12 by decide,
      show plane490GenSourceBasis (671 : Fin 713) = [256, 129, 96, 17, 8, 5, 2] by decide]
  exact space1477_lower

theorem plane490_sourceBlock020 (offset : Fin 32)
    (hlt : 20 * 32 + offset.val < 713) :
    plane490GenConfig.sourceLb (Fin.mk (20 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (Fin.mk (20 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane490_source0640
  | ⟨1, _⟩ => intro hlt; exact plane490_source0641
  | ⟨2, _⟩ => intro hlt; exact plane490_source0642
  | ⟨3, _⟩ => intro hlt; exact plane490_source0643
  | ⟨4, _⟩ => intro hlt; exact plane490_source0644
  | ⟨5, _⟩ => intro hlt; exact plane490_source0645
  | ⟨6, _⟩ => intro hlt; exact plane490_source0646
  | ⟨7, _⟩ => intro hlt; exact plane490_source0647
  | ⟨8, _⟩ => intro hlt; exact plane490_source0648
  | ⟨9, _⟩ => intro hlt; exact plane490_source0649
  | ⟨10, _⟩ => intro hlt; exact plane490_source0650
  | ⟨11, _⟩ => intro hlt; exact plane490_source0651
  | ⟨12, _⟩ => intro hlt; exact plane490_source0652
  | ⟨13, _⟩ => intro hlt; exact plane490_source0653
  | ⟨14, _⟩ => intro hlt; exact plane490_source0654
  | ⟨15, _⟩ => intro hlt; exact plane490_source0655
  | ⟨16, _⟩ => intro hlt; exact plane490_source0656
  | ⟨17, _⟩ => intro hlt; exact plane490_source0657
  | ⟨18, _⟩ => intro hlt; exact plane490_source0658
  | ⟨19, _⟩ => intro hlt; exact plane490_source0659
  | ⟨20, _⟩ => intro hlt; exact plane490_source0660
  | ⟨21, _⟩ => intro hlt; exact plane490_source0661
  | ⟨22, _⟩ => intro hlt; exact plane490_source0662
  | ⟨23, _⟩ => intro hlt; exact plane490_source0663
  | ⟨24, _⟩ => intro hlt; exact plane490_source0664
  | ⟨25, _⟩ => intro hlt; exact plane490_source0665
  | ⟨26, _⟩ => intro hlt; exact plane490_source0666
  | ⟨27, _⟩ => intro hlt; exact plane490_source0667
  | ⟨28, _⟩ => intro hlt; exact plane490_source0668
  | ⟨29, _⟩ => intro hlt; exact plane490_source0669
  | ⟨30, _⟩ => intro hlt; exact plane490_source0670
  | ⟨31, _⟩ => intro hlt; exact plane490_source0671
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
