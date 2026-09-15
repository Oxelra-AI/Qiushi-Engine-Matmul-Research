import QiushiPlane491GenData
import QiushiFrozenWangSpaces046
import QiushiFrozenWangSpaces049
import QiushiFrozenWangSpaces060
import QiushiFrozenWangSpaces084
import QiushiFrozenWangSpaces085
import QiushiFrozenWangSpaces136
import QiushiFrozenWangSpaces137

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane491_source0512 : plane491GenConfig.sourceLb (512 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (512 : Fin 726)) := by
  change plane491GenSourceLb (512 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (512 : Fin 726)))
  rw [show plane491GenSourceLb (512 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (512 : Fin 726) = [264, 129, 72, 32, 24, 4, 2] by decide]
  exact space4367_lower

theorem plane491_source0513 : plane491GenConfig.sourceLb (513 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (513 : Fin 726)) := by
  change plane491GenSourceLb (513 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (513 : Fin 726)))
  rw [show plane491GenSourceLb (513 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (513 : Fin 726) = [257, 128, 64, 33, 17, 5, 2] by decide]
  exact space4368_lower

theorem plane491_source0514 : plane491GenConfig.sourceLb (514 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (514 : Fin 726)) := by
  change plane491GenSourceLb (514 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (514 : Fin 726)))
  rw [show plane491GenSourceLb (514 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (514 : Fin 726) = [265, 128, 72, 33, 25, 5, 2] by decide]
  exact space4369_lower

theorem plane491_source0515 : plane491GenConfig.sourceLb (515 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (515 : Fin 726)) := by
  change plane491GenSourceLb (515 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (515 : Fin 726)))
  rw [show plane491GenSourceLb (515 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (515 : Fin 726) = [256, 129, 64, 33, 16, 4, 3] by decide]
  exact space4370_lower

theorem plane491_source0516 : plane491GenConfig.sourceLb (516 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (516 : Fin 726)) := by
  change plane491GenSourceLb (516 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (516 : Fin 726)))
  rw [show plane491GenSourceLb (516 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (516 : Fin 726) = [264, 136, 65, 40, 17, 4, 3] by decide]
  exact space4371_lower

theorem plane491_source0517 : plane491GenConfig.sourceLb (517 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (517 : Fin 726)) := by
  change plane491GenSourceLb (517 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (517 : Fin 726)))
  rw [show plane491GenSourceLb (517 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (517 : Fin 726) = [265, 128, 72, 32, 24, 4, 3] by decide]
  exact space4372_lower

theorem plane491_source0518 : plane491GenConfig.sourceLb (518 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (518 : Fin 726)) := by
  change plane491GenSourceLb (518 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (518 : Fin 726)))
  rw [show plane491GenSourceLb (518 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (518 : Fin 726) = [256, 136, 73, 40, 24, 5, 3] by decide]
  exact space4373_lower

theorem plane491_source0519 : plane491GenConfig.sourceLb (519 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (519 : Fin 726)) := by
  change plane491GenSourceLb (519 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (519 : Fin 726)))
  rw [show plane491GenSourceLb (519 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (519 : Fin 726) = [264, 129, 72, 33, 25, 5, 3] by decide]
  exact space4374_lower

theorem plane491_source0520 : plane491GenConfig.sourceLb (520 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (520 : Fin 726)) := by
  change plane491GenSourceLb (520 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (520 : Fin 726)))
  rw [show plane491GenSourceLb (520 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (520 : Fin 726) = [257, 136, 72, 40, 25, 5, 3] by decide]
  exact space4375_lower

theorem plane491_source0521 : plane491GenConfig.sourceLb (521 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (521 : Fin 726)) := by
  change plane491GenSourceLb (521 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (521 : Fin 726)))
  rw [show plane491GenSourceLb (521 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (521 : Fin 726) = [264, 137, 65, 42, 18, 7] by decide]
  exact space4376_lower

theorem plane491_source0522 : plane491GenConfig.sourceLb (522 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (522 : Fin 726)) := by
  change plane491GenSourceLb (522 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (522 : Fin 726)))
  rw [show plane491GenSourceLb (522 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (522 : Fin 726) = [256, 128, 64, 35, 16, 4] by decide]
  exact space4377_lower

theorem plane491_source0523 : plane491GenConfig.sourceLb (523 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (523 : Fin 726)) := by
  change plane491GenSourceLb (523 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (523 : Fin 726)))
  rw [show plane491GenSourceLb (523 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (523 : Fin 726) = [257, 136, 73, 40, 24, 5, 3] by decide]
  exact space4378_lower

theorem plane491_source0524 : plane491GenConfig.sourceLb (524 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (524 : Fin 726)) := by
  change plane491GenSourceLb (524 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (524 : Fin 726)))
  rw [show plane491GenSourceLb (524 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (524 : Fin 726) = [256, 137, 73, 41, 25, 4, 3] by decide]
  exact space4379_lower

theorem plane491_source0525 : plane491GenConfig.sourceLb (525 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (525 : Fin 726)) := by
  change plane491GenSourceLb (525 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (525 : Fin 726)))
  rw [show plane491GenSourceLb (525 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (525 : Fin 726) = [265, 128, 73, 33, 24, 5, 2] by decide]
  exact space4380_lower

theorem plane491_source0526 : plane491GenConfig.sourceLb (526 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (526 : Fin 726)) := by
  change plane491GenSourceLb (526 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (526 : Fin 726)))
  rw [show plane491GenSourceLb (526 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (526 : Fin 726) = [257, 128, 65, 33, 17, 4, 2] by decide]
  exact space4381_lower

theorem plane491_source0527 : plane491GenConfig.sourceLb (527 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (527 : Fin 726)) := by
  change plane491GenSourceLb (527 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (527 : Fin 726)))
  rw [show plane491GenSourceLb (527 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (527 : Fin 726) = [257, 137, 72, 40, 24, 4, 2] by decide]
  exact space4382_lower

theorem plane491_source0528 : plane491GenConfig.sourceLb (528 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (528 : Fin 726)) := by
  change plane491GenSourceLb (528 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (528 : Fin 726)))
  rw [show plane491GenSourceLb (528 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (528 : Fin 726) = [266, 138, 64, 40, 18, 6, 1] by decide]
  exact space4383_lower

theorem plane491_source0529 : plane491GenConfig.sourceLb (529 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (529 : Fin 726)) := by
  change plane491GenSourceLb (529 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (529 : Fin 726)))
  rw [show plane491GenSourceLb (529 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (529 : Fin 726) = [260, 140, 72, 44, 28, 2, 1] by decide]
  exact space4384_lower

theorem plane491_source0530 : plane491GenConfig.sourceLb (530 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (530 : Fin 726)) := by
  change plane491GenSourceLb (530 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (530 : Fin 726)))
  rw [show plane491GenSourceLb (530 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (530 : Fin 726) = [260, 132, 68, 38, 16, 10, 1] by decide]
  exact space4385_lower

theorem plane491_source0531 : plane491GenConfig.sourceLb (531 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (531 : Fin 726)) := by
  change plane491GenSourceLb (531 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (531 : Fin 726)))
  rw [show plane491GenSourceLb (531 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (531 : Fin 726) = [256, 134, 68, 36, 16, 12, 1] by decide]
  exact space4386_lower

theorem plane491_source0532 : plane491GenConfig.sourceLb (532 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (532 : Fin 726)) := by
  change plane491GenSourceLb (532 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (532 : Fin 726)))
  rw [show plane491GenSourceLb (532 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (532 : Fin 726) = [260, 134, 64, 36, 20, 12, 1] by decide]
  exact space4387_lower

theorem plane491_source0533 : plane491GenConfig.sourceLb (533 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (533 : Fin 726)) := by
  change plane491GenSourceLb (533 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (533 : Fin 726)))
  rw [show plane491GenSourceLb (533 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (533 : Fin 726) = [258, 130, 66, 32, 22, 12, 1] by decide]
  exact space4388_lower

theorem plane491_source0534 : plane491GenConfig.sourceLb (534 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (534 : Fin 726)) := by
  change plane491GenSourceLb (534 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (534 : Fin 726)))
  rw [show plane491GenSourceLb (534 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (534 : Fin 726) = [262, 134, 64, 36, 20, 14, 1] by decide]
  exact space4389_lower

theorem plane491_source0535 : plane491GenConfig.sourceLb (535 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (535 : Fin 726)) := by
  change plane491GenSourceLb (535 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (535 : Fin 726)))
  rw [show plane491GenSourceLb (535 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (535 : Fin 726) = [261, 133, 69, 36, 17, 8, 2] by decide]
  exact space4390_lower

theorem plane491_source0536 : plane491GenConfig.sourceLb (536 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (536 : Fin 726)) := by
  change plane491GenSourceLb (536 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (536 : Fin 726)))
  rw [show plane491GenSourceLb (536 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (536 : Fin 726) = [256, 132, 65, 37, 21, 8, 2] by decide]
  exact space2744_lower

theorem plane491_source0537 : plane491GenConfig.sourceLb (537 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (537 : Fin 726)) := by
  change plane491GenSourceLb (537 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (537 : Fin 726)))
  rw [show plane491GenSourceLb (537 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (537 : Fin 726) = [256, 133, 64, 37, 20, 8, 3] by decide]
  exact space4391_lower

theorem plane491_source0538 : plane491GenConfig.sourceLb (538 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (538 : Fin 726)) := by
  change plane491GenSourceLb (538 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (538 : Fin 726)))
  rw [show plane491GenSourceLb (538 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (538 : Fin 726) = [257, 133, 65, 37, 21, 8, 3] by decide]
  exact space4392_lower

theorem plane491_source0539 : plane491GenConfig.sourceLb (539 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (539 : Fin 726)) := by
  change plane491GenSourceLb (539 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (539 : Fin 726)))
  rw [show plane491GenSourceLb (539 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (539 : Fin 726) = [256, 128, 68, 32, 16, 9, 3] by decide]
  exact space1571_lower

theorem plane491_source0540 : plane491GenConfig.sourceLb (540 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (540 : Fin 726)) := by
  change plane491GenSourceLb (540 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (540 : Fin 726)))
  rw [show plane491GenSourceLb (540 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (540 : Fin 726) = [257, 129, 68, 33, 16, 9, 3] by decide]
  exact space1488_lower

theorem plane491_source0541 : plane491GenConfig.sourceLb (541 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (541 : Fin 726)) := by
  change plane491GenSourceLb (541 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (541 : Fin 726)))
  rw [show plane491GenSourceLb (541 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (541 : Fin 726) = [256, 132, 64, 36, 20, 9, 3] by decide]
  exact space1948_lower

theorem plane491_source0542 : plane491GenConfig.sourceLb (542 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (542 : Fin 726)) := by
  change plane491GenSourceLb (542 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (542 : Fin 726)))
  rw [show plane491GenSourceLb (542 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (542 : Fin 726) = [261, 128, 65, 32, 21, 9, 3] by decide]
  exact space2696_lower

theorem plane491_source0543 : plane491GenConfig.sourceLb (543 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (543 : Fin 726)) := by
  change plane491GenSourceLb (543 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (543 : Fin 726)))
  rw [show plane491GenSourceLb (543 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (543 : Fin 726) = [261, 128, 69, 32, 17, 13, 3] by decide]
  exact space4393_lower

theorem plane491_sourceBlock016 (offset : Fin 32)
    (hlt : 16 * 32 + offset.val < 726) :
    plane491GenConfig.sourceLb (Fin.mk (16 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (Fin.mk (16 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane491_source0512
  | ⟨1, _⟩ => intro hlt; exact plane491_source0513
  | ⟨2, _⟩ => intro hlt; exact plane491_source0514
  | ⟨3, _⟩ => intro hlt; exact plane491_source0515
  | ⟨4, _⟩ => intro hlt; exact plane491_source0516
  | ⟨5, _⟩ => intro hlt; exact plane491_source0517
  | ⟨6, _⟩ => intro hlt; exact plane491_source0518
  | ⟨7, _⟩ => intro hlt; exact plane491_source0519
  | ⟨8, _⟩ => intro hlt; exact plane491_source0520
  | ⟨9, _⟩ => intro hlt; exact plane491_source0521
  | ⟨10, _⟩ => intro hlt; exact plane491_source0522
  | ⟨11, _⟩ => intro hlt; exact plane491_source0523
  | ⟨12, _⟩ => intro hlt; exact plane491_source0524
  | ⟨13, _⟩ => intro hlt; exact plane491_source0525
  | ⟨14, _⟩ => intro hlt; exact plane491_source0526
  | ⟨15, _⟩ => intro hlt; exact plane491_source0527
  | ⟨16, _⟩ => intro hlt; exact plane491_source0528
  | ⟨17, _⟩ => intro hlt; exact plane491_source0529
  | ⟨18, _⟩ => intro hlt; exact plane491_source0530
  | ⟨19, _⟩ => intro hlt; exact plane491_source0531
  | ⟨20, _⟩ => intro hlt; exact plane491_source0532
  | ⟨21, _⟩ => intro hlt; exact plane491_source0533
  | ⟨22, _⟩ => intro hlt; exact plane491_source0534
  | ⟨23, _⟩ => intro hlt; exact plane491_source0535
  | ⟨24, _⟩ => intro hlt; exact plane491_source0536
  | ⟨25, _⟩ => intro hlt; exact plane491_source0537
  | ⟨26, _⟩ => intro hlt; exact plane491_source0538
  | ⟨27, _⟩ => intro hlt; exact plane491_source0539
  | ⟨28, _⟩ => intro hlt; exact plane491_source0540
  | ⟨29, _⟩ => intro hlt; exact plane491_source0541
  | ⟨30, _⟩ => intro hlt; exact plane491_source0542
  | ⟨31, _⟩ => intro hlt; exact plane491_source0543
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
