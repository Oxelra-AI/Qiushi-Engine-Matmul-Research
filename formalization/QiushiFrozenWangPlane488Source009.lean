import QiushiPlane488GenData
import QiushiFrozenWangSpaces030
import QiushiFrozenWangSpaces031
import QiushiFrozenWangSpaces034
import QiushiFrozenWangSpaces041
import QiushiFrozenWangSpaces047
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces083
import QiushiFrozenWangSpaces084
import QiushiFrozenWangSpaces095

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source0288 : plane488GenConfig.sourceLb (288 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (288 : Fin 413)) := by
  change plane488GenSourceLb (288 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (288 : Fin 413)))
  rw [show plane488GenSourceLb (288 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (288 : Fin 413) = [257, 131, 64, 32, 19, 10, 7] by decide]
  exact space1011_lower

theorem plane488_source0289 : plane488GenConfig.sourceLb (289 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (289 : Fin 413)) := by
  change plane488GenSourceLb (289 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (289 : Fin 413)))
  rw [show plane488GenSourceLb (289 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (289 : Fin 413) = [257, 128, 66, 34, 17, 10, 4] by decide]
  exact space3050_lower

theorem plane488_source0290 : plane488GenConfig.sourceLb (290 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (290 : Fin 413)) := by
  change plane488GenSourceLb (290 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (290 : Fin 413)))
  rw [show plane488GenSourceLb (290 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (290 : Fin 413) = [257, 132, 68, 36, 21, 8, 2] by decide]
  exact space3051_lower

theorem plane488_source0291 : plane488GenConfig.sourceLb (291 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (291 : Fin 413)) := by
  change plane488GenSourceLb (291 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (291 : Fin 413)))
  rw [show plane488GenSourceLb (291 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (291 : Fin 413) = [261, 129, 69, 37, 20, 9, 3] by decide]
  exact space3052_lower

theorem plane488_source0292 : plane488GenConfig.sourceLb (292 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (292 : Fin 413)) := by
  change plane488GenSourceLb (292 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (292 : Fin 413)))
  rw [show plane488GenSourceLb (292 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (292 : Fin 413) = [257, 130, 64, 32, 19, 10, 7] by decide]
  exact space0978_lower

theorem plane488_source0293 : plane488GenConfig.sourceLb (293 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (293 : Fin 413)) := by
  change plane488GenSourceLb (293 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (293 : Fin 413)))
  rw [show plane488GenSourceLb (293 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (293 : Fin 413) = [259, 129, 64, 32, 19, 10, 6] by decide]
  exact space0967_lower

theorem plane488_source0294 : plane488GenConfig.sourceLb (294 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (294 : Fin 413)) := by
  change plane488GenSourceLb (294 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (294 : Fin 413)))
  rw [show plane488GenSourceLb (294 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (294 : Fin 413) = [259, 130, 64, 32, 19, 10, 5] by decide]
  exact space0964_lower

theorem plane488_source0295 : plane488GenConfig.sourceLb (295 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (295 : Fin 413)) := by
  change plane488GenSourceLb (295 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (295 : Fin 413)))
  rw [show plane488GenSourceLb (295 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (295 : Fin 413) = [257, 64, 32, 17, 8, 4, 2] by decide]
  exact space1112_lower

theorem plane488_source0296 : plane488GenConfig.sourceLb (296 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (296 : Fin 413)) := by
  change plane488GenSourceLb (296 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (296 : Fin 413)))
  rw [show plane488GenSourceLb (296 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (296 : Fin 413) = [258, 128, 64, 32, 10, 6, 1] by decide]
  exact space3053_lower

theorem plane488_source0297 : plane488GenConfig.sourceLb (297 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (297 : Fin 413)) := by
  change plane488GenSourceLb (297 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (297 : Fin 413)))
  rw [show plane488GenSourceLb (297 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (297 : Fin 413) = [256, 130, 64, 32, 10, 6, 1] by decide]
  exact space3054_lower

theorem plane488_source0298 : plane488GenConfig.sourceLb (298 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (298 : Fin 413)) := by
  change plane488GenSourceLb (298 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (298 : Fin 413)))
  rw [show plane488GenSourceLb (298 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (298 : Fin 413) = [257, 129, 65, 33, 8, 5, 2] by decide]
  exact space3055_lower

theorem plane488_source0299 : plane488GenConfig.sourceLb (299 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (299 : Fin 413)) := by
  change plane488GenSourceLb (299 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (299 : Fin 413)))
  rw [show plane488GenSourceLb (299 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (299 : Fin 413) = [256, 128, 65, 33, 9, 4, 3] by decide]
  exact space3056_lower

theorem plane488_source0300 : plane488GenConfig.sourceLb (300 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (300 : Fin 413)) := by
  change plane488GenSourceLb (300 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (300 : Fin 413)))
  rw [show plane488GenSourceLb (300 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (300 : Fin 413) = [272, 129, 80, 48, 9, 4, 3] by decide]
  exact space2679_lower

theorem plane488_source0301 : plane488GenConfig.sourceLb (301 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (301 : Fin 413)) := by
  change plane488GenSourceLb (301 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (301 : Fin 413)))
  rw [show plane488GenSourceLb (301 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (301 : Fin 413) = [256, 144, 80, 48, 9, 4, 3] by decide]
  exact space2684_lower

theorem plane488_source0302 : plane488GenConfig.sourceLb (302 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (302 : Fin 413)) := by
  change plane488GenSourceLb (302 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (302 : Fin 413)))
  rw [show plane488GenSourceLb (302 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (302 : Fin 413) = [273, 128, 81, 49, 8, 5, 2] by decide]
  exact space2685_lower

theorem plane488_source0303 : plane488GenConfig.sourceLb (303 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (303 : Fin 413)) := by
  change plane488GenSourceLb (303 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (303 : Fin 413)))
  rw [show plane488GenSourceLb (303 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (303 : Fin 413) = [274, 146, 64, 32, 10, 6, 1] by decide]
  exact space3057_lower

theorem plane488_source0304 : plane488GenConfig.sourceLb (304 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (304 : Fin 413)) := by
  change plane488GenSourceLb (304 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (304 : Fin 413)))
  rw [show plane488GenSourceLb (304 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (304 : Fin 413) = [272, 144, 64, 32, 10, 6, 1] by decide]
  exact space3058_lower

theorem plane488_source0305 : plane488GenConfig.sourceLb (305 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (305 : Fin 413)) := by
  change plane488GenSourceLb (305 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (305 : Fin 413)))
  rw [show plane488GenSourceLb (305 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (305 : Fin 413) = [260, 130, 68, 36, 18, 10, 1] by decide]
  exact space1603_lower

theorem plane488_source0306 : plane488GenConfig.sourceLb (306 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (306 : Fin 413)) := by
  change plane488GenSourceLb (306 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (306 : Fin 413)))
  rw [show plane488GenSourceLb (306 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (306 : Fin 413) = [260, 128, 65, 33, 20, 9, 3] by decide]
  exact space3059_lower

theorem plane488_source0307 : plane488GenConfig.sourceLb (307 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (307 : Fin 413)) := by
  change plane488GenSourceLb (307 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (307 : Fin 413)))
  rw [show plane488GenSourceLb (307 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (307 : Fin 413) = [256, 128, 68, 36, 21, 9, 3] by decide]
  exact space3060_lower

theorem plane488_source0308 : plane488GenConfig.sourceLb (308 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (308 : Fin 413)) := by
  change plane488GenSourceLb (308 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (308 : Fin 413)))
  rw [show plane488GenSourceLb (308 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (308 : Fin 413) = [261, 128, 65, 33, 20, 9, 3] by decide]
  exact space1993_lower

theorem plane488_source0309 : plane488GenConfig.sourceLb (309 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (309 : Fin 413)) := by
  change plane488GenSourceLb (309 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (309 : Fin 413)))
  rw [show plane488GenSourceLb (309 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (309 : Fin 413) = [256, 133, 65, 33, 20, 9, 3] by decide]
  exact space1992_lower

theorem plane488_source0310 : plane488GenConfig.sourceLb (310 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (310 : Fin 413)) := by
  change plane488GenSourceLb (310 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (310 : Fin 413)))
  rw [show plane488GenSourceLb (310 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (310 : Fin 413) = [257, 129, 68, 36, 20, 9, 3] by decide]
  exact space2220_lower

theorem plane488_source0311 : plane488GenConfig.sourceLb (311 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (311 : Fin 413)) := by
  change plane488GenSourceLb (311 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (311 : Fin 413)))
  rw [show plane488GenSourceLb (311 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (311 : Fin 413) = [260, 129, 64, 32, 20, 8, 2] by decide]
  exact space3061_lower

theorem plane488_source0312 : plane488GenConfig.sourceLb (312 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (312 : Fin 413)) := by
  change plane488GenSourceLb (312 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (312 : Fin 413)))
  rw [show plane488GenSourceLb (312 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (312 : Fin 413) = [260, 133, 68, 36, 20, 8, 2] by decide]
  exact space3062_lower

theorem plane488_source0313 : plane488GenConfig.sourceLb (313 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (313 : Fin 413)) := by
  change plane488GenSourceLb (313 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (313 : Fin 413)))
  rw [show plane488GenSourceLb (313 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (313 : Fin 413) = [256, 128, 66, 34, 18, 10, 4] by decide]
  exact space2702_lower

theorem plane488_source0314 : plane488GenConfig.sourceLb (314 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (314 : Fin 413)) := by
  change plane488GenSourceLb (314 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (314 : Fin 413)))
  rw [show plane488GenSourceLb (314 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (314 : Fin 413) = [259, 130, 66, 34, 19, 10, 4] by decide]
  exact space1322_lower

theorem plane488_source0315 : plane488GenConfig.sourceLb (315 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (315 : Fin 413)) := by
  change plane488GenSourceLb (315 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (315 : Fin 413)))
  rw [show plane488GenSourceLb (315 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (315 : Fin 413) = [257, 130, 64, 32, 18, 10, 5] by decide]
  exact space3063_lower

theorem plane488_source0316 : plane488GenConfig.sourceLb (316 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (316 : Fin 413)) := by
  change plane488GenSourceLb (316 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (316 : Fin 413)))
  rw [show plane488GenSourceLb (316 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (316 : Fin 413) = [256, 130, 64, 32, 16, 10, 6] by decide]
  exact space3064_lower

theorem plane488_source0317 : plane488GenConfig.sourceLb (317 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (317 : Fin 413)) := by
  change plane488GenSourceLb (317 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (317 : Fin 413)))
  rw [show plane488GenSourceLb (317 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (317 : Fin 413) = [257, 128, 65, 33, 18, 10, 6] by decide]
  exact space1997_lower

theorem plane488_source0318 : plane488GenConfig.sourceLb (318 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (318 : Fin 413)) := by
  change plane488GenSourceLb (318 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (318 : Fin 413)))
  rw [show plane488GenSourceLb (318 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (318 : Fin 413) = [258, 130, 64, 32, 19, 10, 7] by decide]
  exact space1514_lower

theorem plane488_source0319 : plane488GenConfig.sourceLb (319 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (319 : Fin 413)) := by
  change plane488GenSourceLb (319 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (319 : Fin 413)))
  rw [show plane488GenSourceLb (319 : Fin 413) = 12 by decide,
      show plane488GenSourceBasis (319 : Fin 413) = [259, 131, 64, 32, 19, 10, 7] by decide]
  exact space1513_lower

theorem plane488_sourceBlock009 (offset : Fin 32)
    (hlt : 9 * 32 + offset.val < 413) :
    plane488GenConfig.sourceLb (Fin.mk (9 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (Fin.mk (9 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane488_source0288
  | ⟨1, _⟩ => intro hlt; exact plane488_source0289
  | ⟨2, _⟩ => intro hlt; exact plane488_source0290
  | ⟨3, _⟩ => intro hlt; exact plane488_source0291
  | ⟨4, _⟩ => intro hlt; exact plane488_source0292
  | ⟨5, _⟩ => intro hlt; exact plane488_source0293
  | ⟨6, _⟩ => intro hlt; exact plane488_source0294
  | ⟨7, _⟩ => intro hlt; exact plane488_source0295
  | ⟨8, _⟩ => intro hlt; exact plane488_source0296
  | ⟨9, _⟩ => intro hlt; exact plane488_source0297
  | ⟨10, _⟩ => intro hlt; exact plane488_source0298
  | ⟨11, _⟩ => intro hlt; exact plane488_source0299
  | ⟨12, _⟩ => intro hlt; exact plane488_source0300
  | ⟨13, _⟩ => intro hlt; exact plane488_source0301
  | ⟨14, _⟩ => intro hlt; exact plane488_source0302
  | ⟨15, _⟩ => intro hlt; exact plane488_source0303
  | ⟨16, _⟩ => intro hlt; exact plane488_source0304
  | ⟨17, _⟩ => intro hlt; exact plane488_source0305
  | ⟨18, _⟩ => intro hlt; exact plane488_source0306
  | ⟨19, _⟩ => intro hlt; exact plane488_source0307
  | ⟨20, _⟩ => intro hlt; exact plane488_source0308
  | ⟨21, _⟩ => intro hlt; exact plane488_source0309
  | ⟨22, _⟩ => intro hlt; exact plane488_source0310
  | ⟨23, _⟩ => intro hlt; exact plane488_source0311
  | ⟨24, _⟩ => intro hlt; exact plane488_source0312
  | ⟨25, _⟩ => intro hlt; exact plane488_source0313
  | ⟨26, _⟩ => intro hlt; exact plane488_source0314
  | ⟨27, _⟩ => intro hlt; exact plane488_source0315
  | ⟨28, _⟩ => intro hlt; exact plane488_source0316
  | ⟨29, _⟩ => intro hlt; exact plane488_source0317
  | ⟨30, _⟩ => intro hlt; exact plane488_source0318
  | ⟨31, _⟩ => intro hlt; exact plane488_source0319
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
