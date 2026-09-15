import QiushiPlane485GenData
import QiushiFrozenWangSpaces040
import QiushiFrozenWangSpaces041
import QiushiFrozenWangSpaces042
import QiushiFrozenWangSpaces043
import QiushiFrozenWangSpaces061

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane485_source0320 : plane485GenConfig.sourceLb (320 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (320 : Fin 421)) := by
  change plane485GenSourceLb (320 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (320 : Fin 421)))
  rw [show plane485GenSourceLb (320 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (320 : Fin 421) = [256, 130, 64, 32, 18, 10, 6] by decide]
  exact space1960_lower

theorem plane485_source0321 : plane485GenConfig.sourceLb (321 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (321 : Fin 421)) := by
  change plane485GenSourceLb (321 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (321 : Fin 421)))
  rw [show plane485GenSourceLb (321 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (321 : Fin 421) = [256, 128, 66, 32, 18, 10, 6] by decide]
  exact space1961_lower

theorem plane485_source0322 : plane485GenConfig.sourceLb (322 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (322 : Fin 421)) := by
  change plane485GenSourceLb (322 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (322 : Fin 421)))
  rw [show plane485GenSourceLb (322 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (322 : Fin 421) = [258, 130, 64, 35, 19, 10, 7] by decide]
  exact space1280_lower

theorem plane485_source0323 : plane485GenConfig.sourceLb (323 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (323 : Fin 421)) := by
  change plane485GenSourceLb (323 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (323 : Fin 421)))
  rw [show plane485GenSourceLb (323 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (323 : Fin 421) = [258, 131, 65, 35, 19, 10, 7] by decide]
  exact space1282_lower

theorem plane485_source0324 : plane485GenConfig.sourceLb (324 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (324 : Fin 421)) := by
  change plane485GenSourceLb (324 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (324 : Fin 421)))
  rw [show plane485GenSourceLb (324 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (324 : Fin 421) = [256, 130, 66, 35, 19, 10, 7] by decide]
  exact space1284_lower

theorem plane485_source0325 : plane485GenConfig.sourceLb (325 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (325 : Fin 421)) := by
  change plane485GenSourceLb (325 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (325 : Fin 421)))
  rw [show plane485GenSourceLb (325 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (325 : Fin 421) = [256, 131, 67, 33, 16, 10, 4] by decide]
  exact space1962_lower

theorem plane485_source0326 : plane485GenConfig.sourceLb (326 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (326 : Fin 421)) := by
  change plane485GenSourceLb (326 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (326 : Fin 421)))
  rw [show plane485GenSourceLb (326 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (326 : Fin 421) = [258, 130, 65, 32, 16, 10, 4] by decide]
  exact space1963_lower

theorem plane485_source0327 : plane485GenConfig.sourceLb (327 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (327 : Fin 421)) := by
  change plane485GenSourceLb (327 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (327 : Fin 421)))
  rw [show plane485GenSourceLb (327 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (327 : Fin 421) = [258, 128, 67, 32, 16, 10, 4] by decide]
  exact space1964_lower

theorem plane485_source0328 : plane485GenConfig.sourceLb (328 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (328 : Fin 421)) := by
  change plane485GenSourceLb (328 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (328 : Fin 421)))
  rw [show plane485GenSourceLb (328 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (328 : Fin 421) = [257, 130, 64, 34, 16, 10, 4] by decide]
  exact space1965_lower

theorem plane485_source0329 : plane485GenConfig.sourceLb (329 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (329 : Fin 421)) := by
  change plane485GenSourceLb (329 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (329 : Fin 421)))
  rw [show plane485GenSourceLb (329 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (329 : Fin 421) = [256, 129, 66, 34, 16, 10, 4] by decide]
  exact space1966_lower

theorem plane485_source0330 : plane485GenConfig.sourceLb (330 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (330 : Fin 421)) := by
  change plane485GenSourceLb (330 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (330 : Fin 421)))
  rw [show plane485GenSourceLb (330 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (330 : Fin 421) = [259, 130, 66, 34, 16, 10, 4] by decide]
  exact space1967_lower

theorem plane485_source0331 : plane485GenConfig.sourceLb (331 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (331 : Fin 421)) := by
  change plane485GenSourceLb (331 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (331 : Fin 421)))
  rw [show plane485GenSourceLb (331 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (331 : Fin 421) = [257, 129, 64, 34, 19, 10, 7] by decide]
  exact space1333_lower

theorem plane485_source0332 : plane485GenConfig.sourceLb (332 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (332 : Fin 421)) := by
  change plane485GenSourceLb (332 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (332 : Fin 421)))
  rw [show plane485GenSourceLb (332 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (332 : Fin 421) = [259, 128, 67, 34, 19, 10, 7] by decide]
  exact space1335_lower

theorem plane485_source0333 : plane485GenConfig.sourceLb (333 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (333 : Fin 421)) := by
  change plane485GenSourceLb (333 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (333 : Fin 421)))
  rw [show plane485GenSourceLb (333 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (333 : Fin 421) = [258, 130, 67, 32, 18, 10, 6] by decide]
  exact space1968_lower

theorem plane485_source0334 : plane485GenConfig.sourceLb (334 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (334 : Fin 421)) := by
  change plane485GenSourceLb (334 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (334 : Fin 421)))
  rw [show plane485GenSourceLb (334 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (334 : Fin 421) = [288, 128, 66, 18, 10, 6, 1] by decide]
  exact space1362_lower

theorem plane485_source0335 : plane485GenConfig.sourceLb (335 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (335 : Fin 421)) := by
  change plane485GenSourceLb (335 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (335 : Fin 421)))
  rw [show plane485GenSourceLb (335 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (335 : Fin 421) = [256, 131, 67, 32, 18, 10, 6] by decide]
  exact space1969_lower

theorem plane485_source0336 : plane485GenConfig.sourceLb (336 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (336 : Fin 421)) := by
  change plane485GenSourceLb (336 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (336 : Fin 421)))
  rw [show plane485GenSourceLb (336 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (336 : Fin 421) = [256, 129, 65, 32, 18, 10, 6] by decide]
  exact space1970_lower

theorem plane485_source0337 : plane485GenConfig.sourceLb (337 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (337 : Fin 421)) := by
  change plane485GenSourceLb (337 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (337 : Fin 421)))
  rw [show plane485GenSourceLb (337 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (337 : Fin 421) = [256, 130, 67, 33, 18, 10, 6] by decide]
  exact space1971_lower

theorem plane485_source0338 : plane485GenConfig.sourceLb (338 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (338 : Fin 421)) := by
  change plane485GenSourceLb (338 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (338 : Fin 421)))
  rw [show plane485GenSourceLb (338 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (338 : Fin 421) = [259, 130, 64, 33, 18, 10, 6] by decide]
  exact space1972_lower

theorem plane485_source0339 : plane485GenConfig.sourceLb (339 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (339 : Fin 421)) := by
  change plane485GenSourceLb (339 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (339 : Fin 421)))
  rw [show plane485GenSourceLb (339 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (339 : Fin 421) = [259, 130, 66, 34, 19, 10, 7] by decide]
  exact space1389_lower

theorem plane485_source0340 : plane485GenConfig.sourceLb (340 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (340 : Fin 421)) := by
  change plane485GenSourceLb (340 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (340 : Fin 421)))
  rw [show plane485GenSourceLb (340 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (340 : Fin 421) = [257, 128, 66, 34, 19, 10, 7] by decide]
  exact space1390_lower

theorem plane485_source0341 : plane485GenConfig.sourceLb (341 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (341 : Fin 421)) := by
  change plane485GenSourceLb (341 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (341 : Fin 421)))
  rw [show plane485GenSourceLb (341 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (341 : Fin 421) = [256, 131, 64, 34, 19, 10, 7] by decide]
  exact space1393_lower

theorem plane485_source0342 : plane485GenConfig.sourceLb (342 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (342 : Fin 421)) := by
  change plane485GenSourceLb (342 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (342 : Fin 421)))
  rw [show plane485GenSourceLb (342 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (342 : Fin 421) = [257, 131, 65, 34, 19, 10, 7] by decide]
  exact space1395_lower

theorem plane485_source0343 : plane485GenConfig.sourceLb (343 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (343 : Fin 421)) := by
  change plane485GenSourceLb (343 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (343 : Fin 421)))
  rw [show plane485GenSourceLb (343 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (343 : Fin 421) = [258, 131, 67, 35, 19, 10, 7] by decide]
  exact space1399_lower

theorem plane485_source0344 : plane485GenConfig.sourceLb (344 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (344 : Fin 421)) := by
  change plane485GenSourceLb (344 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (344 : Fin 421)))
  rw [show plane485GenSourceLb (344 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (344 : Fin 421) = [259, 128, 67, 34, 16, 10, 4] by decide]
  exact space1973_lower

theorem plane485_source0345 : plane485GenConfig.sourceLb (345 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (345 : Fin 421)) := by
  change plane485GenSourceLb (345 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (345 : Fin 421)))
  rw [show plane485GenSourceLb (345 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (345 : Fin 421) = [258, 131, 65, 34, 16, 10, 4] by decide]
  exact space1974_lower

theorem plane485_source0346 : plane485GenConfig.sourceLb (346 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (346 : Fin 421)) := by
  change plane485GenSourceLb (346 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (346 : Fin 421)))
  rw [show plane485GenSourceLb (346 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (346 : Fin 421) = [257, 128, 65, 34, 16, 10, 4] by decide]
  exact space1975_lower

theorem plane485_source0347 : plane485GenConfig.sourceLb (347 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (347 : Fin 421)) := by
  change plane485GenSourceLb (347 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (347 : Fin 421)))
  rw [show plane485GenSourceLb (347 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (347 : Fin 421) = [259, 128, 64, 33, 16, 10, 4] by decide]
  exact space1976_lower

theorem plane485_source0348 : plane485GenConfig.sourceLb (348 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (348 : Fin 421)) := by
  change plane485GenSourceLb (348 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (348 : Fin 421)))
  rw [show plane485GenSourceLb (348 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (348 : Fin 421) = [257, 131, 65, 33, 16, 10, 4] by decide]
  exact space1977_lower

theorem plane485_source0349 : plane485GenConfig.sourceLb (349 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (349 : Fin 421)) := by
  change plane485GenSourceLb (349 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (349 : Fin 421)))
  rw [show plane485GenSourceLb (349 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (349 : Fin 421) = [258, 130, 65, 34, 17, 10, 5] by decide]
  exact space1978_lower

theorem plane485_source0350 : plane485GenConfig.sourceLb (350 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (350 : Fin 421)) := by
  change plane485GenSourceLb (350 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (350 : Fin 421)))
  rw [show plane485GenSourceLb (350 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (350 : Fin 421) = [257, 129, 64, 35, 17, 10, 5] by decide]
  exact space1979_lower

theorem plane485_source0351 : plane485GenConfig.sourceLb (351 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (351 : Fin 421)) := by
  change plane485GenSourceLb (351 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (351 : Fin 421)))
  rw [show plane485GenSourceLb (351 : Fin 421) = 12 by decide,
      show plane485GenSourceBasis (351 : Fin 421) = [259, 130, 65, 35, 17, 10, 5] by decide]
  exact space1980_lower

theorem plane485_sourceBlock010 (offset : Fin 32)
    (hlt : 10 * 32 + offset.val < 421) :
    plane485GenConfig.sourceLb (Fin.mk (10 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (Fin.mk (10 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane485_source0320
  | ⟨1, _⟩ => intro hlt; exact plane485_source0321
  | ⟨2, _⟩ => intro hlt; exact plane485_source0322
  | ⟨3, _⟩ => intro hlt; exact plane485_source0323
  | ⟨4, _⟩ => intro hlt; exact plane485_source0324
  | ⟨5, _⟩ => intro hlt; exact plane485_source0325
  | ⟨6, _⟩ => intro hlt; exact plane485_source0326
  | ⟨7, _⟩ => intro hlt; exact plane485_source0327
  | ⟨8, _⟩ => intro hlt; exact plane485_source0328
  | ⟨9, _⟩ => intro hlt; exact plane485_source0329
  | ⟨10, _⟩ => intro hlt; exact plane485_source0330
  | ⟨11, _⟩ => intro hlt; exact plane485_source0331
  | ⟨12, _⟩ => intro hlt; exact plane485_source0332
  | ⟨13, _⟩ => intro hlt; exact plane485_source0333
  | ⟨14, _⟩ => intro hlt; exact plane485_source0334
  | ⟨15, _⟩ => intro hlt; exact plane485_source0335
  | ⟨16, _⟩ => intro hlt; exact plane485_source0336
  | ⟨17, _⟩ => intro hlt; exact plane485_source0337
  | ⟨18, _⟩ => intro hlt; exact plane485_source0338
  | ⟨19, _⟩ => intro hlt; exact plane485_source0339
  | ⟨20, _⟩ => intro hlt; exact plane485_source0340
  | ⟨21, _⟩ => intro hlt; exact plane485_source0341
  | ⟨22, _⟩ => intro hlt; exact plane485_source0342
  | ⟨23, _⟩ => intro hlt; exact plane485_source0343
  | ⟨24, _⟩ => intro hlt; exact plane485_source0344
  | ⟨25, _⟩ => intro hlt; exact plane485_source0345
  | ⟨26, _⟩ => intro hlt; exact plane485_source0346
  | ⟨27, _⟩ => intro hlt; exact plane485_source0347
  | ⟨28, _⟩ => intro hlt; exact plane485_source0348
  | ⟨29, _⟩ => intro hlt; exact plane485_source0349
  | ⟨30, _⟩ => intro hlt; exact plane485_source0350
  | ⟨31, _⟩ => intro hlt; exact plane485_source0351
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
