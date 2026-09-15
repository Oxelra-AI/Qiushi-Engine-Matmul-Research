import QiushiPlane491GenData
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces083
import QiushiFrozenWangSpaces085
import QiushiFrozenWangSpaces086
import QiushiFrozenWangSpaces087
import QiushiFrozenWangSpaces135
import QiushiFrozenWangSpaces136

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane491_source0480 : plane491GenConfig.sourceLb (480 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (480 : Fin 726)) := by
  change plane491GenSourceLb (480 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (480 : Fin 726)))
  rw [show plane491GenSourceLb (480 : Fin 726) = 14 by decide,
      show plane491GenSourceBasis (480 : Fin 726) = [262, 132, 70, 38, 18, 12, 1] by decide]
  exact space4340_lower

theorem plane491_source0481 : plane491GenConfig.sourceLb (481 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (481 : Fin 726)) := by
  change plane491GenSourceLb (481 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (481 : Fin 726)))
  rw [show plane491GenSourceLb (481 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (481 : Fin 726) = [128, 68, 32, 16, 8, 3] by decide]
  exact space4341_lower

theorem plane491_source0482 : plane491GenConfig.sourceLb (482 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (482 : Fin 726)) := by
  change plane491GenSourceLb (482 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (482 : Fin 726)))
  rw [show plane491GenSourceLb (482 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (482 : Fin 726) = [132, 68, 36, 16, 12, 2, 1] by decide]
  exact space4342_lower

theorem plane491_source0483 : plane491GenConfig.sourceLb (483 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (483 : Fin 726)) := by
  change plane491GenSourceLb (483 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (483 : Fin 726)))
  rw [show plane491GenSourceLb (483 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (483 : Fin 726) = [131, 64, 32, 19, 8, 7] by decide]
  exact space4343_lower

theorem plane491_source0484 : plane491GenConfig.sourceLb (484 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (484 : Fin 726)) := by
  change plane491GenSourceLb (484 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (484 : Fin 726)))
  rw [show plane491GenSourceLb (484 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (484 : Fin 726) = [128, 66, 34, 18, 8, 4, 1] by decide]
  exact space4344_lower

theorem plane491_source0485 : plane491GenConfig.sourceLb (485 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (485 : Fin 726)) := by
  change plane491GenSourceLb (485 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (485 : Fin 726)))
  rw [show plane491GenSourceLb (485 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (485 : Fin 726) = [128, 66, 34, 16, 8, 6, 1] by decide]
  exact space4345_lower

theorem plane491_source0486 : plane491GenConfig.sourceLb (486 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (486 : Fin 726)) := by
  change plane491GenSourceLb (486 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (486 : Fin 726)))
  rw [show plane491GenSourceLb (486 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (486 : Fin 726) = [129, 65, 32, 16, 9, 5, 2] by decide]
  exact space4346_lower

theorem plane491_source0487 : plane491GenConfig.sourceLb (487 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (487 : Fin 726)) := by
  change plane491GenSourceLb (487 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (487 : Fin 726)))
  rw [show plane491GenSourceLb (487 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (487 : Fin 726) = [129, 64, 33, 16, 8, 4, 3] by decide]
  exact space4347_lower

theorem plane491_source0488 : plane491GenConfig.sourceLb (488 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (488 : Fin 726)) := by
  change plane491GenSourceLb (488 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (488 : Fin 726)))
  rw [show plane491GenSourceLb (488 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (488 : Fin 726) = [132, 68, 36, 16, 8, 3] by decide]
  exact space4348_lower

theorem plane491_source0489 : plane491GenConfig.sourceLb (489 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (489 : Fin 726)) := by
  change plane491GenSourceLb (489 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (489 : Fin 726)))
  rw [show plane491GenSourceLb (489 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (489 : Fin 726) = [132, 64, 36, 20, 12, 2, 1] by decide]
  exact space4349_lower

theorem plane491_source0490 : plane491GenConfig.sourceLb (490 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (490 : Fin 726)) := by
  change plane491GenSourceLb (490 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (490 : Fin 726)))
  rw [show plane491GenSourceLb (490 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (490 : Fin 726) = [258, 162, 66, 16, 10, 6, 1] by decide]
  exact space2786_lower

theorem plane491_source0491 : plane491GenConfig.sourceLb (491 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (491 : Fin 726)) := by
  change plane491GenSourceLb (491 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (491 : Fin 726)))
  rw [show plane491GenSourceLb (491 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (491 : Fin 726) = [256, 162, 64, 16, 10, 4, 1] by decide]
  exact space2013_lower

theorem plane491_source0492 : plane491GenConfig.sourceLb (492 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (492 : Fin 726)) := by
  change plane491GenSourceLb (492 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (492 : Fin 726)))
  rw [show plane491GenSourceLb (492 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (492 : Fin 726) = [273, 144, 80, 49, 8, 4, 2] by decide]
  exact space2747_lower

theorem plane491_source0493 : plane491GenConfig.sourceLb (493 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (493 : Fin 726)) := by
  change plane491GenSourceLb (493 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (493 : Fin 726)))
  rw [show plane491GenSourceLb (493 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (493 : Fin 726) = [257, 129, 80, 33, 9, 4, 3] by decide]
  exact space2678_lower

theorem plane491_source0494 : plane491GenConfig.sourceLb (494 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (494 : Fin 726)) := by
  change plane491GenSourceLb (494 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (494 : Fin 726)))
  rw [show plane491GenSourceLb (494 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (494 : Fin 726) = [273, 145, 81, 49, 8, 5, 3] by decide]
  exact space4350_lower

theorem plane491_source0495 : plane491GenConfig.sourceLb (495 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (495 : Fin 726)) := by
  change plane491GenSourceLb (495 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (495 : Fin 726)))
  rw [show plane491GenSourceLb (495 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (495 : Fin 726) = [273, 145, 81, 49, 9, 5, 3] by decide]
  exact space2770_lower

theorem plane491_source0496 : plane491GenConfig.sourceLb (496 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (496 : Fin 726)) := by
  change plane491GenSourceLb (496 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (496 : Fin 726)))
  rw [show plane491GenSourceLb (496 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (496 : Fin 726) = [273, 144, 81, 48, 8, 5, 3] by decide]
  exact space4351_lower

theorem plane491_source0497 : plane491GenConfig.sourceLb (497 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (497 : Fin 726)) := by
  change plane491GenSourceLb (497 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (497 : Fin 726)))
  rw [show plane491GenSourceLb (497 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (497 : Fin 726) = [257, 128, 80, 32, 9, 4, 3] by decide]
  exact space4352_lower

theorem plane491_source0498 : plane491GenConfig.sourceLb (498 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (498 : Fin 726)) := by
  change plane491GenSourceLb (498 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (498 : Fin 726)))
  rw [show plane491GenSourceLb (498 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (498 : Fin 726) = [273, 145, 81, 48, 9, 5, 2] by decide]
  exact space4353_lower

theorem plane491_source0499 : plane491GenConfig.sourceLb (499 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (499 : Fin 726)) := by
  change plane491GenSourceLb (499 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (499 : Fin 726)))
  rw [show plane491GenSourceLb (499 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (499 : Fin 726) = [273, 144, 80, 49, 9, 4, 2] by decide]
  exact space4354_lower

theorem plane491_source0500 : plane491GenConfig.sourceLb (500 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (500 : Fin 726)) := by
  change plane491GenSourceLb (500 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (500 : Fin 726)))
  rw [show plane491GenSourceLb (500 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (500 : Fin 726) = [272, 145, 80, 48, 9, 4, 2] by decide]
  exact space4355_lower

theorem plane491_source0501 : plane491GenConfig.sourceLb (501 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (501 : Fin 726)) := by
  change plane491GenSourceLb (501 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (501 : Fin 726)))
  rw [show plane491GenSourceLb (501 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (501 : Fin 726) = [272, 146, 82, 48, 8, 6, 1] by decide]
  exact space4356_lower

theorem plane491_source0502 : plane491GenConfig.sourceLb (502 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (502 : Fin 726)) := by
  change plane491GenSourceLb (502 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (502 : Fin 726)))
  rw [show plane491GenSourceLb (502 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (502 : Fin 726) = [258, 128, 80, 34, 10, 4, 1] by decide]
  exact space4357_lower

theorem plane491_source0503 : plane491GenConfig.sourceLb (503 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (503 : Fin 726)) := by
  change plane491GenSourceLb (503 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (503 : Fin 726)))
  rw [show plane491GenSourceLb (503 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (503 : Fin 726) = [274, 144, 80, 50, 10, 4, 1] by decide]
  exact space4358_lower

theorem plane491_source0504 : plane491GenConfig.sourceLb (504 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (504 : Fin 726)) := by
  change plane491GenSourceLb (504 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (504 : Fin 726)))
  rw [show plane491GenSourceLb (504 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (504 : Fin 726) = [258, 130, 80, 32, 8, 4, 1] by decide]
  exact space4359_lower

theorem plane491_source0505 : plane491GenConfig.sourceLb (505 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (505 : Fin 726)) := by
  change plane491GenSourceLb (505 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (505 : Fin 726)))
  rw [show plane491GenSourceLb (505 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (505 : Fin 726) = [274, 146, 80, 48, 8, 4, 1] by decide]
  exact space4360_lower

theorem plane491_source0506 : plane491GenConfig.sourceLb (506 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (506 : Fin 726)) := by
  change plane491GenSourceLb (506 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (506 : Fin 726)))
  rw [show plane491GenSourceLb (506 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (506 : Fin 726) = [256, 140, 72, 44, 28, 2, 1] by decide]
  exact space4361_lower

theorem plane491_source0507 : plane491GenConfig.sourceLb (507 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (507 : Fin 726)) := by
  change plane491GenSourceLb (507 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (507 : Fin 726)))
  rw [show plane491GenSourceLb (507 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (507 : Fin 726) = [256, 130, 65, 33, 17, 4] by decide]
  exact space4362_lower

theorem plane491_source0508 : plane491GenConfig.sourceLb (508 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (508 : Fin 726)) := by
  change plane491GenSourceLb (508 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (508 : Fin 726)))
  rw [show plane491GenSourceLb (508 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (508 : Fin 726) = [256, 128, 66, 34, 18, 4, 1] by decide]
  exact space4363_lower

theorem plane491_source0509 : plane491GenConfig.sourceLb (509 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (509 : Fin 726)) := by
  change plane491GenSourceLb (509 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (509 : Fin 726)))
  rw [show plane491GenSourceLb (509 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (509 : Fin 726) = [256, 128, 66, 34, 16, 6, 1] by decide]
  exact space4364_lower

theorem plane491_source0510 : plane491GenConfig.sourceLb (510 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (510 : Fin 726)) := by
  change plane491GenSourceLb (510 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (510 : Fin 726)))
  rw [show plane491GenSourceLb (510 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (510 : Fin 726) = [264, 130, 72, 32, 26, 6, 1] by decide]
  exact space4365_lower

theorem plane491_source0511 : plane491GenConfig.sourceLb (511 : Fin 726) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (511 : Fin 726)) := by
  change plane491GenSourceLb (511 : Fin 726) ≤
    frozenWangTable.L0 (spanCodes (plane491GenSourceBasis (511 : Fin 726)))
  rw [show plane491GenSourceLb (511 : Fin 726) = 12 by decide,
      show plane491GenSourceBasis (511 : Fin 726) = [257, 129, 65, 32, 17, 4, 2] by decide]
  exact space4366_lower

theorem plane491_sourceBlock015 (offset : Fin 32)
    (hlt : 15 * 32 + offset.val < 726) :
    plane491GenConfig.sourceLb (Fin.mk (15 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane491GenConfig.sourceU (Fin.mk (15 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane491_source0480
  | ⟨1, _⟩ => intro hlt; exact plane491_source0481
  | ⟨2, _⟩ => intro hlt; exact plane491_source0482
  | ⟨3, _⟩ => intro hlt; exact plane491_source0483
  | ⟨4, _⟩ => intro hlt; exact plane491_source0484
  | ⟨5, _⟩ => intro hlt; exact plane491_source0485
  | ⟨6, _⟩ => intro hlt; exact plane491_source0486
  | ⟨7, _⟩ => intro hlt; exact plane491_source0487
  | ⟨8, _⟩ => intro hlt; exact plane491_source0488
  | ⟨9, _⟩ => intro hlt; exact plane491_source0489
  | ⟨10, _⟩ => intro hlt; exact plane491_source0490
  | ⟨11, _⟩ => intro hlt; exact plane491_source0491
  | ⟨12, _⟩ => intro hlt; exact plane491_source0492
  | ⟨13, _⟩ => intro hlt; exact plane491_source0493
  | ⟨14, _⟩ => intro hlt; exact plane491_source0494
  | ⟨15, _⟩ => intro hlt; exact plane491_source0495
  | ⟨16, _⟩ => intro hlt; exact plane491_source0496
  | ⟨17, _⟩ => intro hlt; exact plane491_source0497
  | ⟨18, _⟩ => intro hlt; exact plane491_source0498
  | ⟨19, _⟩ => intro hlt; exact plane491_source0499
  | ⟨20, _⟩ => intro hlt; exact plane491_source0500
  | ⟨21, _⟩ => intro hlt; exact plane491_source0501
  | ⟨22, _⟩ => intro hlt; exact plane491_source0502
  | ⟨23, _⟩ => intro hlt; exact plane491_source0503
  | ⟨24, _⟩ => intro hlt; exact plane491_source0504
  | ⟨25, _⟩ => intro hlt; exact plane491_source0505
  | ⟨26, _⟩ => intro hlt; exact plane491_source0506
  | ⟨27, _⟩ => intro hlt; exact plane491_source0507
  | ⟨28, _⟩ => intro hlt; exact plane491_source0508
  | ⟨29, _⟩ => intro hlt; exact plane491_source0509
  | ⟨30, _⟩ => intro hlt; exact plane491_source0510
  | ⟨31, _⟩ => intro hlt; exact plane491_source0511
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
