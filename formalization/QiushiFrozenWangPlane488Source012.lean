import QiushiPlane488GenData
import QiushiFrozenWangSpaces042
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces052
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces063
import QiushiFrozenWangSpaces087
import QiushiFrozenWangSpaces096
import QiushiFrozenWangSpaces097

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source0384 : plane488GenConfig.sourceLb (384 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (384 : Fin 413)) := by
  change plane488GenSourceLb (384 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (384 : Fin 413)))
  rw [show plane488GenSourceLb (384 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (384 : Fin 413) = [262, 130, 64, 32, 18, 10, 1] by decide]
  exact space1356_lower

theorem plane488_source0385 : plane488GenConfig.sourceLb (385 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (385 : Fin 413)) := by
  change plane488GenSourceLb (385 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (385 : Fin 413)))
  rw [show plane488GenSourceLb (385 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (385 : Fin 413) = [262, 134, 70, 38, 16, 10, 1] by decide]
  exact space3103_lower

theorem plane488_source0386 : plane488GenConfig.sourceLb (386 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (386 : Fin 413)) := by
  change plane488GenSourceLb (386 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (386 : Fin 413)))
  rw [show plane488GenSourceLb (386 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (386 : Fin 413) = [272, 130, 66, 34, 10, 6, 1] by decide]
  exact space3104_lower

theorem plane488_source0387 : plane488GenConfig.sourceLb (387 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (387 : Fin 413)) := by
  change plane488GenSourceLb (387 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (387 : Fin 413)))
  rw [show plane488GenSourceLb (387 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (387 : Fin 413) = [274, 128, 66, 34, 10, 6, 1] by decide]
  exact space3105_lower

theorem plane488_source0388 : plane488GenConfig.sourceLb (388 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (388 : Fin 413)) := by
  change plane488GenSourceLb (388 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (388 : Fin 413)))
  rw [show plane488GenSourceLb (388 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (388 : Fin 413) = [386, 64, 32, 18, 10, 6, 1] by decide]
  exact space1365_lower

theorem plane488_source0389 : plane488GenConfig.sourceLb (389 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (389 : Fin 413)) := by
  change plane488GenSourceLb (389 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (389 : Fin 413)))
  rw [show plane488GenSourceLb (389 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (389 : Fin 413) = [256, 144, 66, 34, 10, 4, 1] by decide]
  exact space3106_lower

theorem plane488_source0390 : plane488GenConfig.sourceLb (390 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (390 : Fin 413)) := by
  change plane488GenSourceLb (390 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (390 : Fin 413)))
  rw [show plane488GenSourceLb (390 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (390 : Fin 413) = [260, 132, 68, 36, 20, 8, 2, 1] by decide]
  exact space2015_lower

theorem plane488_source0391 : plane488GenConfig.sourceLb (391 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (391 : Fin 413)) := by
  change plane488GenSourceLb (391 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (391 : Fin 413)))
  rw [show plane488GenSourceLb (391 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (391 : Fin 413) = [259, 131, 64, 32, 18, 10, 7] by decide]
  exact space3107_lower

theorem plane488_source0392 : plane488GenConfig.sourceLb (392 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (392 : Fin 413)) := by
  change plane488GenSourceLb (392 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (392 : Fin 413)))
  rw [show plane488GenSourceLb (392 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (392 : Fin 413) = [258, 128, 64, 32, 18, 10, 4, 1] by decide]
  exact space1664_lower

theorem plane488_source0393 : plane488GenConfig.sourceLb (393 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (393 : Fin 413)) := by
  change plane488GenSourceLb (393 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (393 : Fin 413)))
  rw [show plane488GenSourceLb (393 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (393 : Fin 413) = [258, 128, 66, 34, 18, 10, 6, 1] by decide]
  exact space1625_lower

theorem plane488_source0394 : plane488GenConfig.sourceLb (394 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (394 : Fin 413)) := by
  change plane488GenSourceLb (394 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (394 : Fin 413)))
  rw [show plane488GenSourceLb (394 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (394 : Fin 413) = [256, 130, 66, 34, 18, 10, 6, 1] by decide]
  exact space1626_lower

theorem plane488_source0395 : plane488GenConfig.sourceLb (395 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (395 : Fin 413)) := by
  change plane488GenSourceLb (395 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (395 : Fin 413)))
  rw [show plane488GenSourceLb (395 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (395 : Fin 413) = [257, 128, 64, 32, 17, 8, 4, 2] by decide]
  exact space1658_lower

theorem plane488_source0396 : plane488GenConfig.sourceLb (396 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (396 : Fin 413)) := by
  change plane488GenSourceLb (396 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (396 : Fin 413)))
  rw [show plane488GenSourceLb (396 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (396 : Fin 413) = [257, 129, 65, 33, 16, 8, 5, 2] by decide]
  exact space3108_lower

theorem plane488_source0397 : plane488GenConfig.sourceLb (397 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (397 : Fin 413)) := by
  change plane488GenSourceLb (397 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (397 : Fin 413)))
  rw [show plane488GenSourceLb (397 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (397 : Fin 413) = [257, 129, 64, 32, 17, 8, 5, 2] by decide]
  exact space1654_lower

theorem plane488_source0398 : plane488GenConfig.sourceLb (398 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (398 : Fin 413)) := by
  change plane488GenSourceLb (398 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (398 : Fin 413)))
  rw [show plane488GenSourceLb (398 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (398 : Fin 413) = [257, 129, 65, 33, 16, 9, 4, 3] by decide]
  exact space1643_lower

theorem plane488_source0399 : plane488GenConfig.sourceLb (399 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (399 : Fin 413)) := by
  change plane488GenSourceLb (399 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (399 : Fin 413)))
  rw [show plane488GenSourceLb (399 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (399 : Fin 413) = [257, 128, 65, 33, 17, 9, 4, 3] by decide]
  exact space2793_lower

theorem plane488_source0400 : plane488GenConfig.sourceLb (400 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (400 : Fin 413)) := by
  change plane488GenSourceLb (400 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (400 : Fin 413)))
  rw [show plane488GenSourceLb (400 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (400 : Fin 413) = [256, 129, 65, 33, 16, 9, 5, 3] by decide]
  exact space1639_lower

theorem plane488_source0401 : plane488GenConfig.sourceLb (401 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (401 : Fin 413)) := by
  change plane488GenSourceLb (401 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (401 : Fin 413)))
  rw [show plane488GenSourceLb (401 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (401 : Fin 413) = [256, 129, 64, 32, 17, 9, 5, 3] by decide]
  exact space2021_lower

theorem plane488_source0402 : plane488GenConfig.sourceLb (402 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (402 : Fin 413)) := by
  change plane488GenSourceLb (402 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (402 : Fin 413)))
  rw [show plane488GenSourceLb (402 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (402 : Fin 413) = [257, 129, 64, 32, 17, 9, 5, 3] by decide]
  exact space2018_lower

theorem plane488_source0403 : plane488GenConfig.sourceLb (403 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (403 : Fin 413)) := by
  change plane488GenSourceLb (403 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (403 : Fin 413)))
  rw [show plane488GenSourceLb (403 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (403 : Fin 413) = [257, 128, 64, 32, 16, 9, 5, 3] by decide]
  exact space1642_lower

theorem plane488_source0404 : plane488GenConfig.sourceLb (404 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (404 : Fin 413)) := by
  change plane488GenSourceLb (404 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (404 : Fin 413)))
  rw [show plane488GenSourceLb (404 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (404 : Fin 413) = [256, 128, 65, 33, 17, 9, 4, 3] by decide]
  exact space3109_lower

theorem plane488_source0405 : plane488GenConfig.sourceLb (405 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (405 : Fin 413)) := by
  change plane488GenSourceLb (405 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (405 : Fin 413)))
  rw [show plane488GenSourceLb (405 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (405 : Fin 413) = [257, 129, 64, 32, 16, 9, 4, 3] by decide]
  exact space1648_lower

theorem plane488_source0406 : plane488GenConfig.sourceLb (406 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (406 : Fin 413)) := by
  change plane488GenSourceLb (406 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (406 : Fin 413)))
  rw [show plane488GenSourceLb (406 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (406 : Fin 413) = [257, 129, 65, 33, 17, 8, 5, 2] by decide]
  exact space1649_lower

theorem plane488_source0407 : plane488GenConfig.sourceLb (407 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (407 : Fin 413)) := by
  change plane488GenSourceLb (407 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (407 : Fin 413)))
  rw [show plane488GenSourceLb (407 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (407 : Fin 413) = [257, 128, 64, 32, 17, 8, 5, 2] by decide]
  exact space1631_lower

theorem plane488_source0408 : plane488GenConfig.sourceLb (408 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (408 : Fin 413)) := by
  change plane488GenSourceLb (408 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (408 : Fin 413)))
  rw [show plane488GenSourceLb (408 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (408 : Fin 413) = [257, 129, 64, 32, 17, 8, 4, 2] by decide]
  exact space1627_lower

theorem plane488_source0409 : plane488GenConfig.sourceLb (409 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (409 : Fin 413)) := by
  change plane488GenSourceLb (409 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (409 : Fin 413)))
  rw [show plane488GenSourceLb (409 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (409 : Fin 413) = [256, 130, 64, 32, 18, 10, 6, 1] by decide]
  exact space1622_lower

theorem plane488_source0410 : plane488GenConfig.sourceLb (410 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (410 : Fin 413)) := by
  change plane488GenSourceLb (410 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (410 : Fin 413)))
  rw [show plane488GenSourceLb (410 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (410 : Fin 413) = [258, 128, 64, 32, 18, 10, 6, 1] by decide]
  exact space1621_lower

theorem plane488_source0411 : plane488GenConfig.sourceLb (411 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (411 : Fin 413)) := by
  change plane488GenSourceLb (411 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (411 : Fin 413)))
  rw [show plane488GenSourceLb (411 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (411 : Fin 413) = [258, 130, 64, 32, 18, 10, 4, 1] by decide]
  exact space1617_lower

theorem plane488_source0412 : plane488GenConfig.sourceLb (412 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (412 : Fin 413)) := by
  change plane488GenSourceLb (412 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (412 : Fin 413)))
  rw [show plane488GenSourceLb (412 : Fin 413) = 9 by decide,
      show plane488GenSourceBasis (412 : Fin 413) = [260, 128, 68, 36, 20, 8, 2, 1] by decide]
  exact space2027_lower

theorem plane488_sourceBlock012 (offset : Fin 32)
    (hlt : 12 * 32 + offset.val < 413) :
    plane488GenConfig.sourceLb (Fin.mk (12 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (Fin.mk (12 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane488_source0384
  | ⟨1, _⟩ => intro hlt; exact plane488_source0385
  | ⟨2, _⟩ => intro hlt; exact plane488_source0386
  | ⟨3, _⟩ => intro hlt; exact plane488_source0387
  | ⟨4, _⟩ => intro hlt; exact plane488_source0388
  | ⟨5, _⟩ => intro hlt; exact plane488_source0389
  | ⟨6, _⟩ => intro hlt; exact plane488_source0390
  | ⟨7, _⟩ => intro hlt; exact plane488_source0391
  | ⟨8, _⟩ => intro hlt; exact plane488_source0392
  | ⟨9, _⟩ => intro hlt; exact plane488_source0393
  | ⟨10, _⟩ => intro hlt; exact plane488_source0394
  | ⟨11, _⟩ => intro hlt; exact plane488_source0395
  | ⟨12, _⟩ => intro hlt; exact plane488_source0396
  | ⟨13, _⟩ => intro hlt; exact plane488_source0397
  | ⟨14, _⟩ => intro hlt; exact plane488_source0398
  | ⟨15, _⟩ => intro hlt; exact plane488_source0399
  | ⟨16, _⟩ => intro hlt; exact plane488_source0400
  | ⟨17, _⟩ => intro hlt; exact plane488_source0401
  | ⟨18, _⟩ => intro hlt; exact plane488_source0402
  | ⟨19, _⟩ => intro hlt; exact plane488_source0403
  | ⟨20, _⟩ => intro hlt; exact plane488_source0404
  | ⟨21, _⟩ => intro hlt; exact plane488_source0405
  | ⟨22, _⟩ => intro hlt; exact plane488_source0406
  | ⟨23, _⟩ => intro hlt; exact plane488_source0407
  | ⟨24, _⟩ => intro hlt; exact plane488_source0408
  | ⟨25, _⟩ => intro hlt; exact plane488_source0409
  | ⟨26, _⟩ => intro hlt; exact plane488_source0410
  | ⟨27, _⟩ => intro hlt; exact plane488_source0411
  | ⟨28, _⟩ => intro hlt; exact plane488_source0412
  | ⟨k + 29, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
