import QiushiPlane488GenData
import QiushiFrozenWangSpaces035
import QiushiFrozenWangSpaces036
import QiushiFrozenWangSpaces037
import QiushiFrozenWangSpaces040
import QiushiFrozenWangSpaces043
import QiushiFrozenWangSpaces045
import QiushiFrozenWangSpaces049
import QiushiFrozenWangSpaces061
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces070
import QiushiFrozenWangSpaces086
import QiushiFrozenWangSpaces096

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source0352 : plane488GenConfig.sourceLb (352 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (352 : Fin 413)) := by
  change plane488GenSourceLb (352 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (352 : Fin 413)))
  rw [show plane488GenSourceLb (352 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (352 : Fin 413) = [259, 128, 64, 32, 17, 10, 4] by decide]
  exact space2239_lower

theorem plane488_source0353 : plane488GenConfig.sourceLb (353 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (353 : Fin 413)) := by
  change plane488GenSourceLb (353 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (353 : Fin 413)))
  rw [show plane488GenSourceLb (353 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (353 : Fin 413) = [256, 128, 65, 33, 18, 10, 5] by decide]
  exact space2241_lower

theorem plane488_source0354 : plane488GenConfig.sourceLb (354 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (354 : Fin 413)) := by
  change plane488GenSourceLb (354 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (354 : Fin 413)))
  rw [show plane488GenSourceLb (354 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (354 : Fin 413) = [257, 129, 64, 32, 19, 10, 5] by decide]
  exact space1292_lower

theorem plane488_source0355 : plane488GenConfig.sourceLb (355 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (355 : Fin 413)) := by
  change plane488GenSourceLb (355 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (355 : Fin 413)))
  rw [show plane488GenSourceLb (355 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (355 : Fin 413) = [257, 130, 64, 32, 16, 10, 5] by decide]
  exact space3087_lower

theorem plane488_source0356 : plane488GenConfig.sourceLb (356 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (356 : Fin 413)) := by
  change plane488GenSourceLb (356 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (356 : Fin 413)))
  rw [show plane488GenSourceLb (356 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (356 : Fin 413) = [259, 131, 66, 34, 17, 10, 5] by decide]
  exact space3088_lower

theorem plane488_source0357 : plane488GenConfig.sourceLb (357 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (357 : Fin 413)) := by
  change plane488GenSourceLb (357 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (357 : Fin 413)))
  rw [show plane488GenSourceLb (357 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (357 : Fin 413) = [257, 129, 66, 34, 17, 10, 5] by decide]
  exact space3089_lower

theorem plane488_source0358 : plane488GenConfig.sourceLb (358 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (358 : Fin 413)) := by
  change plane488GenSourceLb (358 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (358 : Fin 413)))
  rw [show plane488GenSourceLb (358 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (358 : Fin 413) = [257, 131, 64, 32, 17, 10, 5] by decide]
  exact space3090_lower

theorem plane488_source0359 : plane488GenConfig.sourceLb (359 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (359 : Fin 413)) := by
  change plane488GenSourceLb (359 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (359 : Fin 413)))
  rw [show plane488GenSourceLb (359 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (359 : Fin 413) = [257, 129, 64, 32, 20, 8, 2] by decide]
  exact space3091_lower

theorem plane488_source0360 : plane488GenConfig.sourceLb (360 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (360 : Fin 413)) := by
  change plane488GenSourceLb (360 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (360 : Fin 413)))
  rw [show plane488GenSourceLb (360 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (360 : Fin 413) = [260, 133, 68, 36, 17, 8, 2] by decide]
  exact space1215_lower

theorem plane488_source0361 : plane488GenConfig.sourceLb (361 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (361 : Fin 413)) := by
  change plane488GenSourceLb (361 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (361 : Fin 413)))
  rw [show plane488GenSourceLb (361 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (361 : Fin 413) = [261, 133, 69, 37, 17, 8, 2] by decide]
  exact space1179_lower

theorem plane488_source0362 : plane488GenConfig.sourceLb (362 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (362 : Fin 413)) := by
  change plane488GenSourceLb (362 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (362 : Fin 413)))
  rw [show plane488GenSourceLb (362 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (362 : Fin 413) = [257, 133, 65, 33, 17, 8, 2] by decide]
  exact space1471_lower

theorem plane488_source0363 : plane488GenConfig.sourceLb (363 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (363 : Fin 413)) := by
  change plane488GenSourceLb (363 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (363 : Fin 413)))
  rw [show plane488GenSourceLb (363 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (363 : Fin 413) = [273, 144, 81, 49, 8, 4, 2] by decide]
  exact space3092_lower

theorem plane488_source0364 : plane488GenConfig.sourceLb (364 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (364 : Fin 413)) := by
  change plane488GenSourceLb (364 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (364 : Fin 413)))
  rw [show plane488GenSourceLb (364 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (364 : Fin 413) = [288, 129, 96, 17, 8, 4, 2] by decide]
  exact space1154_lower

theorem plane488_source0365 : plane488GenConfig.sourceLb (365 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (365 : Fin 413)) := by
  change plane488GenSourceLb (365 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (365 : Fin 413)))
  rw [show plane488GenSourceLb (365 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (365 : Fin 413) = [273, 145, 81, 49, 8, 5, 2] by decide]
  exact space3093_lower

theorem plane488_source0366 : plane488GenConfig.sourceLb (366 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (366 : Fin 413)) := by
  change plane488GenSourceLb (366 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (366 : Fin 413)))
  rw [show plane488GenSourceLb (366 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (366 : Fin 413) = [288, 128, 96, 17, 8, 5, 2] by decide]
  exact space1151_lower

theorem plane488_source0367 : plane488GenConfig.sourceLb (367 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (367 : Fin 413)) := by
  change plane488GenSourceLb (367 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (367 : Fin 413)))
  rw [show plane488GenSourceLb (367 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (367 : Fin 413) = [256, 132, 68, 36, 21, 9, 3] by decide]
  exact space2246_lower

theorem plane488_source0368 : plane488GenConfig.sourceLb (368 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (368 : Fin 413)) := by
  change plane488GenSourceLb (368 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (368 : Fin 413)))
  rw [show plane488GenSourceLb (368 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (368 : Fin 413) = [261, 133, 64, 32, 21, 9, 3] by decide]
  exact space3094_lower

theorem plane488_source0369 : plane488GenConfig.sourceLb (369 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (369 : Fin 413)) := by
  change plane488GenSourceLb (369 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (369 : Fin 413)))
  rw [show plane488GenSourceLb (369 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (369 : Fin 413) = [257, 129, 64, 32, 21, 9, 3] by decide]
  exact space3095_lower

theorem plane488_source0370 : plane488GenConfig.sourceLb (370 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (370 : Fin 413)) := by
  change plane488GenSourceLb (370 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (370 : Fin 413)))
  rw [show plane488GenSourceLb (370 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (370 : Fin 413) = [257, 145, 65, 33, 9, 4, 3] by decide]
  exact space3096_lower

theorem plane488_source0371 : plane488GenConfig.sourceLb (371 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (371 : Fin 413)) := by
  change plane488GenSourceLb (371 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (371 : Fin 413)))
  rw [show plane488GenSourceLb (371 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (371 : Fin 413) = [384, 65, 33, 16, 9, 4, 3] by decide]
  exact space3097_lower

theorem plane488_source0372 : plane488GenConfig.sourceLb (372 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (372 : Fin 413)) := by
  change plane488GenSourceLb (372 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (372 : Fin 413)))
  rw [show plane488GenSourceLb (372 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (372 : Fin 413) = [257, 128, 81, 49, 9, 5, 3] by decide]
  exact space2757_lower

theorem plane488_source0373 : plane488GenConfig.sourceLb (373 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (373 : Fin 413)) := by
  change plane488GenSourceLb (373 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (373 : Fin 413)))
  rw [show plane488GenSourceLb (373 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (373 : Fin 413) = [259, 130, 66, 34, 19, 10, 7] by decide]
  exact space1389_lower

theorem plane488_source0374 : plane488GenConfig.sourceLb (374 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (374 : Fin 413)) := by
  change plane488GenSourceLb (374 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (374 : Fin 413)))
  rw [show plane488GenSourceLb (374 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (374 : Fin 413) = [259, 130, 67, 35, 18, 10, 7] by decide]
  exact space2247_lower

theorem plane488_source0375 : plane488GenConfig.sourceLb (375 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (375 : Fin 413)) := by
  change plane488GenSourceLb (375 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (375 : Fin 413)))
  rw [show plane488GenSourceLb (375 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (375 : Fin 413) = [257, 130, 66, 34, 16, 10, 6] by decide]
  exact space3098_lower

theorem plane488_source0376 : plane488GenConfig.sourceLb (376 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (376 : Fin 413)) := by
  change plane488GenSourceLb (376 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (376 : Fin 413)))
  rw [show plane488GenSourceLb (376 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (376 : Fin 413) = [258, 130, 64, 32, 18, 10, 5] by decide]
  exact space3099_lower

theorem plane488_source0377 : plane488GenConfig.sourceLb (377 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (377 : Fin 413)) := by
  change plane488GenSourceLb (377 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (377 : Fin 413)))
  rw [show plane488GenSourceLb (377 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (377 : Fin 413) = [257, 129, 66, 34, 16, 10, 5] by decide]
  exact space3100_lower

theorem plane488_source0378 : plane488GenConfig.sourceLb (378 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (378 : Fin 413)) := by
  change plane488GenSourceLb (378 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (378 : Fin 413)))
  rw [show plane488GenSourceLb (378 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (378 : Fin 413) = [257, 131, 64, 32, 16, 10, 5] by decide]
  exact space3101_lower

theorem plane488_source0379 : plane488GenConfig.sourceLb (379 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (379 : Fin 413)) := by
  change plane488GenSourceLb (379 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (379 : Fin 413)))
  rw [show plane488GenSourceLb (379 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (379 : Fin 413) = [259, 130, 66, 34, 16, 10, 4] by decide]
  exact space1967_lower

theorem plane488_source0380 : plane488GenConfig.sourceLb (380 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (380 : Fin 413)) := by
  change plane488GenSourceLb (380 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (380 : Fin 413)))
  rw [show plane488GenSourceLb (380 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (380 : Fin 413) = [261, 129, 64, 32, 16, 9, 3] by decide]
  exact space1572_lower

theorem plane488_source0381 : plane488GenConfig.sourceLb (381 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (381 : Fin 413)) := by
  change plane488GenSourceLb (381 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (381 : Fin 413)))
  rw [show plane488GenSourceLb (381 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (381 : Fin 413) = [273, 145, 81, 49, 9, 5, 3] by decide]
  exact space2770_lower

theorem plane488_source0382 : plane488GenConfig.sourceLb (382 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (382 : Fin 413)) := by
  change plane488GenSourceLb (382 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (382 : Fin 413)))
  rw [show plane488GenSourceLb (382 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (382 : Fin 413) = [257, 144, 64, 32, 9, 5, 3] by decide]
  exact space3102_lower

theorem plane488_source0383 : plane488GenConfig.sourceLb (383 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (383 : Fin 413)) := by
  change plane488GenSourceLb (383 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (383 : Fin 413)))
  rw [show plane488GenSourceLb (383 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (383 : Fin 413) = [385, 64, 32, 16, 9, 5, 3] by decide]
  exact space1576_lower

theorem plane488_sourceBlock011 (offset : Fin 32)
    (hlt : 11 * 32 + offset.val < 413) :
    plane488GenConfig.sourceLb (Fin.mk (11 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (Fin.mk (11 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane488_source0352
  | ⟨1, _⟩ => intro hlt; exact plane488_source0353
  | ⟨2, _⟩ => intro hlt; exact plane488_source0354
  | ⟨3, _⟩ => intro hlt; exact plane488_source0355
  | ⟨4, _⟩ => intro hlt; exact plane488_source0356
  | ⟨5, _⟩ => intro hlt; exact plane488_source0357
  | ⟨6, _⟩ => intro hlt; exact plane488_source0358
  | ⟨7, _⟩ => intro hlt; exact plane488_source0359
  | ⟨8, _⟩ => intro hlt; exact plane488_source0360
  | ⟨9, _⟩ => intro hlt; exact plane488_source0361
  | ⟨10, _⟩ => intro hlt; exact plane488_source0362
  | ⟨11, _⟩ => intro hlt; exact plane488_source0363
  | ⟨12, _⟩ => intro hlt; exact plane488_source0364
  | ⟨13, _⟩ => intro hlt; exact plane488_source0365
  | ⟨14, _⟩ => intro hlt; exact plane488_source0366
  | ⟨15, _⟩ => intro hlt; exact plane488_source0367
  | ⟨16, _⟩ => intro hlt; exact plane488_source0368
  | ⟨17, _⟩ => intro hlt; exact plane488_source0369
  | ⟨18, _⟩ => intro hlt; exact plane488_source0370
  | ⟨19, _⟩ => intro hlt; exact plane488_source0371
  | ⟨20, _⟩ => intro hlt; exact plane488_source0372
  | ⟨21, _⟩ => intro hlt; exact plane488_source0373
  | ⟨22, _⟩ => intro hlt; exact plane488_source0374
  | ⟨23, _⟩ => intro hlt; exact plane488_source0375
  | ⟨24, _⟩ => intro hlt; exact plane488_source0376
  | ⟨25, _⟩ => intro hlt; exact plane488_source0377
  | ⟨26, _⟩ => intro hlt; exact plane488_source0378
  | ⟨27, _⟩ => intro hlt; exact plane488_source0379
  | ⟨28, _⟩ => intro hlt; exact plane488_source0380
  | ⟨29, _⟩ => intro hlt; exact plane488_source0381
  | ⟨30, _⟩ => intro hlt; exact plane488_source0382
  | ⟨31, _⟩ => intro hlt; exact plane488_source0383
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
