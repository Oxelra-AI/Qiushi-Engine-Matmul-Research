import QiushiPlane488GenData
import QiushiFrozenWangSpaces036
import QiushiFrozenWangSpaces041
import QiushiFrozenWangSpaces042
import QiushiFrozenWangSpaces045
import QiushiFrozenWangSpaces061
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces085
import QiushiFrozenWangSpaces095
import QiushiFrozenWangSpaces096

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source0320 : plane488GenConfig.sourceLb (320 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (320 : Fin 413)) := by
  change plane488GenSourceLb (320 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (320 : Fin 413)))
  rw [show plane488GenSourceLb (320 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (320 : Fin 413) = [256, 130, 66, 34, 19, 10, 7] by decide]
  exact space1338_lower

theorem plane488_source0321 : plane488GenConfig.sourceLb (321 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (321 : Fin 413)) := by
  change plane488GenSourceLb (321 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (321 : Fin 413)))
  rw [show plane488GenSourceLb (321 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (321 : Fin 413) = [256, 130, 66, 34, 16, 10, 5] by decide]
  exact space3065_lower

theorem plane488_source0322 : plane488GenConfig.sourceLb (322 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (322 : Fin 413)) := by
  change plane488GenSourceLb (322 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (322 : Fin 413)))
  rw [show plane488GenSourceLb (322 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (322 : Fin 413) = [257, 130, 64, 32, 19, 10, 5] by decide]
  exact space1446_lower

theorem plane488_source0323 : plane488GenConfig.sourceLb (323 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (323 : Fin 413)) := by
  change plane488GenSourceLb (323 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (323 : Fin 413)))
  rw [show plane488GenSourceLb (323 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (323 : Fin 413) = [257, 131, 64, 32, 18, 10, 5] by decide]
  exact space3066_lower

theorem plane488_source0324 : plane488GenConfig.sourceLb (324 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (324 : Fin 413)) := by
  change plane488GenSourceLb (324 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (324 : Fin 413)))
  rw [show plane488GenSourceLb (324 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (324 : Fin 413) = [259, 131, 64, 32, 17, 10, 4] by decide]
  exact space3067_lower

theorem plane488_source0325 : plane488GenConfig.sourceLb (325 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (325 : Fin 413)) := by
  change plane488GenSourceLb (325 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (325 : Fin 413)))
  rw [show plane488GenSourceLb (325 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (325 : Fin 413) = [258, 130, 67, 35, 18, 10, 4] by decide]
  exact space3068_lower

theorem plane488_source0326 : plane488GenConfig.sourceLb (326 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (326 : Fin 413)) := by
  change plane488GenSourceLb (326 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (326 : Fin 413)))
  rw [show plane488GenSourceLb (326 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (326 : Fin 413) = [259, 128, 64, 32, 17, 10, 7] by decide]
  exact space3069_lower

theorem plane488_source0327 : plane488GenConfig.sourceLb (327 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (327 : Fin 413)) := by
  change plane488GenSourceLb (327 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (327 : Fin 413)))
  rw [show plane488GenSourceLb (327 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (327 : Fin 413) = [259, 131, 67, 35, 17, 10, 7] by decide]
  exact space2232_lower

theorem plane488_source0328 : plane488GenConfig.sourceLb (328 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (328 : Fin 413)) := by
  change plane488GenSourceLb (328 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (328 : Fin 413)))
  rw [show plane488GenSourceLb (328 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (328 : Fin 413) = [258, 130, 66, 34, 16, 10, 7] by decide]
  exact space3070_lower

theorem plane488_source0329 : plane488GenConfig.sourceLb (329 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (329 : Fin 413)) := by
  change plane488GenSourceLb (329 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (329 : Fin 413)))
  rw [show plane488GenSourceLb (329 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (329 : Fin 413) = [256, 131, 67, 35, 18, 10, 7] by decide]
  exact space2233_lower

theorem plane488_source0330 : plane488GenConfig.sourceLb (330 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (330 : Fin 413)) := by
  change plane488GenSourceLb (330 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (330 : Fin 413)))
  rw [show plane488GenSourceLb (330 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (330 : Fin 413) = [258, 128, 66, 34, 18, 10, 7] by decide]
  exact space3071_lower

theorem plane488_source0331 : plane488GenConfig.sourceLb (331 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (331 : Fin 413)) := by
  change plane488GenSourceLb (331 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (331 : Fin 413)))
  rw [show plane488GenSourceLb (331 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (331 : Fin 413) = [257, 130, 65, 33, 17, 10, 6] by decide]
  exact space3072_lower

theorem plane488_source0332 : plane488GenConfig.sourceLb (332 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (332 : Fin 413)) := by
  change plane488GenSourceLb (332 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (332 : Fin 413)))
  rw [show plane488GenSourceLb (332 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (332 : Fin 413) = [258, 131, 64, 32, 18, 10, 6] by decide]
  exact space1999_lower

theorem plane488_source0333 : plane488GenConfig.sourceLb (333 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (333 : Fin 413)) := by
  change plane488GenSourceLb (333 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (333 : Fin 413)))
  rw [show plane488GenSourceLb (333 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (333 : Fin 413) = [258, 130, 70, 38, 18, 10, 1] by decide]
  exact space1173_lower

theorem plane488_source0334 : plane488GenConfig.sourceLb (334 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (334 : Fin 413)) := by
  change plane488GenSourceLb (334 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (334 : Fin 413)))
  rw [show plane488GenSourceLb (334 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (334 : Fin 413) = [260, 128, 66, 34, 18, 10, 1] by decide]
  exact space3073_lower

theorem plane488_source0335 : plane488GenConfig.sourceLb (335 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (335 : Fin 413)) := by
  change plane488GenSourceLb (335 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (335 : Fin 413)))
  rw [show plane488GenSourceLb (335 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (335 : Fin 413) = [272, 130, 64, 32, 10, 6, 1] by decide]
  exact space3074_lower

theorem plane488_source0336 : plane488GenConfig.sourceLb (336 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (336 : Fin 413)) := by
  change plane488GenSourceLb (336 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (336 : Fin 413)))
  rw [show plane488GenSourceLb (336 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (336 : Fin 413) = [256, 144, 66, 34, 10, 6, 1] by decide]
  exact space3075_lower

theorem plane488_source0337 : plane488GenConfig.sourceLb (337 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (337 : Fin 413)) := by
  change plane488GenSourceLb (337 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (337 : Fin 413)))
  rw [show plane488GenSourceLb (337 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (337 : Fin 413) = [258, 146, 66, 34, 10, 6, 1] by decide]
  exact space3076_lower

theorem plane488_source0338 : plane488GenConfig.sourceLb (338 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (338 : Fin 413)) := by
  change plane488GenSourceLb (338 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (338 : Fin 413)))
  rw [show plane488GenSourceLb (338 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (338 : Fin 413) = [386, 64, 32, 16, 10, 6, 1] by decide]
  exact space3077_lower

theorem plane488_source0339 : plane488GenConfig.sourceLb (339 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (339 : Fin 413)) := by
  change plane488GenSourceLb (339 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (339 : Fin 413)))
  rw [show plane488GenSourceLb (339 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (339 : Fin 413) = [386, 66, 34, 18, 10, 6, 1] by decide]
  exact space1366_lower

theorem plane488_source0340 : plane488GenConfig.sourceLb (340 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (340 : Fin 413)) := by
  change plane488GenSourceLb (340 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (340 : Fin 413)))
  rw [show plane488GenSourceLb (340 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (340 : Fin 413) = [263, 135, 68, 36, 18, 10] by decide]
  exact space3078_lower

theorem plane488_source0341 : plane488GenConfig.sourceLb (341 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (341 : Fin 413)) := by
  change plane488GenSourceLb (341 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (341 : Fin 413)))
  rw [show plane488GenSourceLb (341 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (341 : Fin 413) = [256, 130, 64, 32, 18, 10, 6] by decide]
  exact space1960_lower

theorem plane488_source0342 : plane488GenConfig.sourceLb (342 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (342 : Fin 413)) := by
  change plane488GenSourceLb (342 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (342 : Fin 413)))
  rw [show plane488GenSourceLb (342 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (342 : Fin 413) = [258, 129, 65, 33, 18, 10, 6] by decide]
  exact space3079_lower

theorem plane488_source0343 : plane488GenConfig.sourceLb (343 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (343 : Fin 413)) := by
  change plane488GenSourceLb (343 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (343 : Fin 413)))
  rw [show plane488GenSourceLb (343 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (343 : Fin 413) = [257, 128, 66, 34, 18, 10, 7] by decide]
  exact space3080_lower

theorem plane488_source0344 : plane488GenConfig.sourceLb (344 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (344 : Fin 413)) := by
  change plane488GenSourceLb (344 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (344 : Fin 413)))
  rw [show plane488GenSourceLb (344 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (344 : Fin 413) = [256, 129, 66, 34, 18, 10, 7] by decide]
  exact space3081_lower

theorem plane488_source0345 : plane488GenConfig.sourceLb (345 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (345 : Fin 413)) := by
  change plane488GenSourceLb (345 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (345 : Fin 413)))
  rw [show plane488GenSourceLb (345 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (345 : Fin 413) = [257, 129, 67, 35, 18, 10, 7] by decide]
  exact space3082_lower

theorem plane488_source0346 : plane488GenConfig.sourceLb (346 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (346 : Fin 413)) := by
  change plane488GenSourceLb (346 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (346 : Fin 413)))
  rw [show plane488GenSourceLb (346 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (346 : Fin 413) = [256, 130, 64, 32, 19, 10, 7] by decide]
  exact space1324_lower

theorem plane488_source0347 : plane488GenConfig.sourceLb (347 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (347 : Fin 413)) := by
  change plane488GenSourceLb (347 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (347 : Fin 413)))
  rw [show plane488GenSourceLb (347 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (347 : Fin 413) = [259, 130, 64, 32, 16, 10, 7] by decide]
  exact space3083_lower

theorem plane488_source0348 : plane488GenConfig.sourceLb (348 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (348 : Fin 413)) := by
  change plane488GenSourceLb (348 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (348 : Fin 413)))
  rw [show plane488GenSourceLb (348 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (348 : Fin 413) = [257, 129, 64, 32, 17, 10, 7] by decide]
  exact space3084_lower

theorem plane488_source0349 : plane488GenConfig.sourceLb (349 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (349 : Fin 413)) := by
  change plane488GenSourceLb (349 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (349 : Fin 413)))
  rw [show plane488GenSourceLb (349 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (349 : Fin 413) = [259, 129, 66, 34, 18, 10, 4] by decide]
  exact space2736_lower

theorem plane488_source0350 : plane488GenConfig.sourceLb (350 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (350 : Fin 413)) := by
  change plane488GenSourceLb (350 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (350 : Fin 413)))
  rw [show plane488GenSourceLb (350 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (350 : Fin 413) = [256, 131, 67, 35, 18, 10, 4] by decide]
  exact space3085_lower

theorem plane488_source0351 : plane488GenConfig.sourceLb (351 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (351 : Fin 413)) := by
  change plane488GenSourceLb (351 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (351 : Fin 413)))
  rw [show plane488GenSourceLb (351 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (351 : Fin 413) = [256, 128, 66, 34, 16, 10, 4] by decide]
  exact space3086_lower

theorem plane488_sourceBlock010 (offset : Fin 32)
    (hlt : 10 * 32 + offset.val < 413) :
    plane488GenConfig.sourceLb (Fin.mk (10 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (Fin.mk (10 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane488_source0320
  | ⟨1, _⟩ => intro hlt; exact plane488_source0321
  | ⟨2, _⟩ => intro hlt; exact plane488_source0322
  | ⟨3, _⟩ => intro hlt; exact plane488_source0323
  | ⟨4, _⟩ => intro hlt; exact plane488_source0324
  | ⟨5, _⟩ => intro hlt; exact plane488_source0325
  | ⟨6, _⟩ => intro hlt; exact plane488_source0326
  | ⟨7, _⟩ => intro hlt; exact plane488_source0327
  | ⟨8, _⟩ => intro hlt; exact plane488_source0328
  | ⟨9, _⟩ => intro hlt; exact plane488_source0329
  | ⟨10, _⟩ => intro hlt; exact plane488_source0330
  | ⟨11, _⟩ => intro hlt; exact plane488_source0331
  | ⟨12, _⟩ => intro hlt; exact plane488_source0332
  | ⟨13, _⟩ => intro hlt; exact plane488_source0333
  | ⟨14, _⟩ => intro hlt; exact plane488_source0334
  | ⟨15, _⟩ => intro hlt; exact plane488_source0335
  | ⟨16, _⟩ => intro hlt; exact plane488_source0336
  | ⟨17, _⟩ => intro hlt; exact plane488_source0337
  | ⟨18, _⟩ => intro hlt; exact plane488_source0338
  | ⟨19, _⟩ => intro hlt; exact plane488_source0339
  | ⟨20, _⟩ => intro hlt; exact plane488_source0340
  | ⟨21, _⟩ => intro hlt; exact plane488_source0341
  | ⟨22, _⟩ => intro hlt; exact plane488_source0342
  | ⟨23, _⟩ => intro hlt; exact plane488_source0343
  | ⟨24, _⟩ => intro hlt; exact plane488_source0344
  | ⟨25, _⟩ => intro hlt; exact plane488_source0345
  | ⟨26, _⟩ => intro hlt; exact plane488_source0346
  | ⟨27, _⟩ => intro hlt; exact plane488_source0347
  | ⟨28, _⟩ => intro hlt; exact plane488_source0348
  | ⟨29, _⟩ => intro hlt; exact plane488_source0349
  | ⟨30, _⟩ => intro hlt; exact plane488_source0350
  | ⟨31, _⟩ => intro hlt; exact plane488_source0351
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
