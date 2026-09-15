import QiushiPlane491GenData
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces087
import QiushiFrozenWangSpaces141

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane491_source0704 : plane491GenConfig.sourceLb (704 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (704 : Fin 726)) := by
  change plane491GenSourceLb (704 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (704 : Fin 726)))
  rw [show plane491GenSourceLb (704 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (704 : Fin 726) = [257, 128, 65, 33, 17, 9, 4, 2] by decide]
  exact space4531_lower

theorem plane491_source0705 : plane491GenConfig.sourceLb (705 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (705 : Fin 726)) := by
  change plane491GenSourceLb (705 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (705 : Fin 726)))
  rw [show plane491GenSourceLb (705 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (705 : Fin 726) = [257, 128, 64, 33, 17, 8, 5, 2] by decide]
  exact space1652_lower

theorem plane491_source0706 : plane491GenConfig.sourceLb (706 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (706 : Fin 726)) := by
  change plane491GenSourceLb (706 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (706 : Fin 726)))
  rw [show plane491GenSourceLb (706 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (706 : Fin 726) = [256, 129, 65, 32, 16, 9, 5, 2] by decide]
  exact space4532_lower

theorem plane491_source0707 : plane491GenConfig.sourceLb (707 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (707 : Fin 726)) := by
  change plane491GenSourceLb (707 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (707 : Fin 726)))
  rw [show plane491GenSourceLb (707 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (707 : Fin 726) = [256, 129, 64, 33, 16, 8, 4, 3] by decide]
  exact space4533_lower

theorem plane491_source0708 : plane491GenConfig.sourceLb (708 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (708 : Fin 726)) := by
  change plane491GenSourceLb (708 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (708 : Fin 726)))
  rw [show plane491GenSourceLb (708 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (708 : Fin 726) = [257, 129, 65, 33, 17, 8, 4, 3] by decide]
  exact space4534_lower

theorem plane491_source0709 : plane491GenConfig.sourceLb (709 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (709 : Fin 726)) := by
  change plane491GenSourceLb (709 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (709 : Fin 726)))
  rw [show plane491GenSourceLb (709 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (709 : Fin 726) = [256, 129, 64, 33, 17, 8, 5, 3] by decide]
  exact space4535_lower

theorem plane491_source0710 : plane491GenConfig.sourceLb (710 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (710 : Fin 726)) := by
  change plane491GenSourceLb (710 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (710 : Fin 726)))
  rw [show plane491GenSourceLb (710 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (710 : Fin 726) = [257, 128, 65, 32, 16, 9, 5, 3] by decide]
  exact space1635_lower

theorem plane491_source0711 : plane491GenConfig.sourceLb (711 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (711 : Fin 726)) := by
  change plane491GenSourceLb (711 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (711 : Fin 726)))
  rw [show plane491GenSourceLb (711 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (711 : Fin 726) = [256, 129, 65, 33, 16, 9, 5, 3] by decide]
  exact space1639_lower

theorem plane491_source0712 : plane491GenConfig.sourceLb (712 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (712 : Fin 726)) := by
  change plane491GenSourceLb (712 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (712 : Fin 726)))
  rw [show plane491GenSourceLb (712 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (712 : Fin 726) = [257, 128, 64, 32, 16, 9, 4, 3] by decide]
  exact space1633_lower

theorem plane491_source0713 : plane491GenConfig.sourceLb (713 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (713 : Fin 726)) := by
  change plane491GenSourceLb (713 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (713 : Fin 726)))
  rw [show plane491GenSourceLb (713 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (713 : Fin 726) = [257, 128, 65, 32, 17, 8, 4, 3] by decide]
  exact space4536_lower

theorem plane491_source0714 : plane491GenConfig.sourceLb (714 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (714 : Fin 726)) := by
  change plane491GenSourceLb (714 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (714 : Fin 726)))
  rw [show plane491GenSourceLb (714 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (714 : Fin 726) = [257, 129, 65, 32, 16, 9, 5, 2] by decide]
  exact space4537_lower

theorem plane491_source0715 : plane491GenConfig.sourceLb (715 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (715 : Fin 726)) := by
  change plane491GenSourceLb (715 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (715 : Fin 726)))
  rw [show plane491GenSourceLb (715 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (715 : Fin 726) = [257, 129, 64, 32, 17, 8, 5, 2] by decide]
  exact space1654_lower

theorem plane491_source0716 : plane491GenConfig.sourceLb (716 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (716 : Fin 726)) := by
  change plane491GenSourceLb (716 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (716 : Fin 726)))
  rw [show plane491GenSourceLb (716 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (716 : Fin 726) = [257, 129, 65, 32, 17, 9, 4, 2] by decide]
  exact space4538_lower

theorem plane491_source0717 : plane491GenConfig.sourceLb (717 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (717 : Fin 726)) := by
  change plane491GenSourceLb (717 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (717 : Fin 726)))
  rw [show plane491GenSourceLb (717 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (717 : Fin 726) = [257, 128, 65, 33, 17, 8, 4, 2] by decide]
  exact space1656_lower

theorem plane491_source0718 : plane491GenConfig.sourceLb (718 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (718 : Fin 726)) := by
  change plane491GenSourceLb (718 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (718 : Fin 726)))
  rw [show plane491GenSourceLb (718 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (718 : Fin 726) = [258, 128, 64, 34, 18, 10, 6, 1] by decide]
  exact space1660_lower

theorem plane491_source0719 : plane491GenConfig.sourceLb (719 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (719 : Fin 726)) := by
  change plane491GenSourceLb (719 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (719 : Fin 726)))
  rw [show plane491GenSourceLb (719 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (719 : Fin 726) = [256, 128, 66, 34, 16, 10, 6, 1] by decide]
  exact space2792_lower

theorem plane491_source0720 : plane491GenConfig.sourceLb (720 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (720 : Fin 726)) := by
  change plane491GenSourceLb (720 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (720 : Fin 726)))
  rw [show plane491GenSourceLb (720 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (720 : Fin 726) = [258, 128, 66, 34, 16, 8, 6, 1] by decide]
  exact space4539_lower

theorem plane491_source0721 : plane491GenConfig.sourceLb (721 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (721 : Fin 726)) := by
  change plane491GenSourceLb (721 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (721 : Fin 726)))
  rw [show plane491GenSourceLb (721 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (721 : Fin 726) = [256, 128, 66, 34, 18, 10, 4, 1] by decide]
  exact space1620_lower

theorem plane491_source0722 : plane491GenConfig.sourceLb (722 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (722 : Fin 726)) := by
  change plane491GenSourceLb (722 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (722 : Fin 726)))
  rw [show plane491GenSourceLb (722 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (722 : Fin 726) = [258, 128, 64, 34, 16, 10, 4, 1] by decide]
  exact space2790_lower

theorem plane491_source0723 : plane491GenConfig.sourceLb (723 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (723 : Fin 726)) := by
  change plane491GenSourceLb (723 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (723 : Fin 726)))
  rw [show plane491GenSourceLb (723 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (723 : Fin 726) = [258, 128, 66, 34, 18, 8, 4, 1] by decide]
  exact space4540_lower

theorem plane491_source0724 : plane491GenConfig.sourceLb (724 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (724 : Fin 726)) := by
  change plane491GenSourceLb (724 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (724 : Fin 726)))
  rw [show plane491GenSourceLb (724 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (724 : Fin 726) = [256, 132, 64, 36, 20, 12, 2, 1] by decide]
  exact space4541_lower

theorem plane491_source0725 : plane491GenConfig.sourceLb (725 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (725 : Fin 726)) := by
  change plane491GenSourceLb (725 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (725 : Fin 726)))
  rw [show plane491GenSourceLb (725 : Fin 726) = 9 by decide,
      show plane491GenSourceBasis (725 : Fin 726) = [260, 132, 68, 36, 16, 12, 2, 1] by decide]
  exact space4542_lower

theorem plane491_sourceBlock022 (offset : Fin 32)
    (hlt : 22 * 32 + offset.val < 726) :
    plane491GenConfig.sourceLb (Fin.mk (22 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (Fin.mk (22 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane491_source0704
  | ⟨1, _⟩ => intro hlt; exact plane491_source0705
  | ⟨2, _⟩ => intro hlt; exact plane491_source0706
  | ⟨3, _⟩ => intro hlt; exact plane491_source0707
  | ⟨4, _⟩ => intro hlt; exact plane491_source0708
  | ⟨5, _⟩ => intro hlt; exact plane491_source0709
  | ⟨6, _⟩ => intro hlt; exact plane491_source0710
  | ⟨7, _⟩ => intro hlt; exact plane491_source0711
  | ⟨8, _⟩ => intro hlt; exact plane491_source0712
  | ⟨9, _⟩ => intro hlt; exact plane491_source0713
  | ⟨10, _⟩ => intro hlt; exact plane491_source0714
  | ⟨11, _⟩ => intro hlt; exact plane491_source0715
  | ⟨12, _⟩ => intro hlt; exact plane491_source0716
  | ⟨13, _⟩ => intro hlt; exact plane491_source0717
  | ⟨14, _⟩ => intro hlt; exact plane491_source0718
  | ⟨15, _⟩ => intro hlt; exact plane491_source0719
  | ⟨16, _⟩ => intro hlt; exact plane491_source0720
  | ⟨17, _⟩ => intro hlt; exact plane491_source0721
  | ⟨18, _⟩ => intro hlt; exact plane491_source0722
  | ⟨19, _⟩ => intro hlt; exact plane491_source0723
  | ⟨20, _⟩ => intro hlt; exact plane491_source0724
  | ⟨21, _⟩ => intro hlt; exact plane491_source0725
  | ⟨k + 22, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
