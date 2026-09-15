import QiushiPlane488GenData
import QiushiFrozenWangSpaces029
import QiushiFrozenWangSpaces030
import QiushiFrozenWangSpaces032
import QiushiFrozenWangSpaces034
import QiushiFrozenWangSpaces081
import QiushiFrozenWangSpaces082
import QiushiFrozenWangSpaces094
import QiushiFrozenWangSpaces095

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane488_source0256 : plane488GenConfig.sourceLb (256 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (256 : Fin 413)) := by
  change plane488GenSourceLb (256 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (256 : Fin 413)))
  rw [show plane488GenSourceLb (256 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (256 : Fin 413) = [258, 145, 66, 34, 10, 4] by decide]
  exact space3028_lower

theorem plane488_source0257 : plane488GenConfig.sourceLb (257 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (257 : Fin 413)) := by
  change plane488GenSourceLb (257 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (257 : Fin 413)))
  rw [show plane488GenSourceLb (257 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (257 : Fin 413) = [258, 148, 66, 34, 10, 1] by decide]
  exact space3029_lower

theorem plane488_source0258 : plane488GenConfig.sourceLb (258 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (258 : Fin 413)) := by
  change plane488GenSourceLb (258 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (258 : Fin 413)))
  rw [show plane488GenSourceLb (258 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (258 : Fin 413) = [258, 178, 96, 10, 4, 1] by decide]
  exact space3030_lower

theorem plane488_source0259 : plane488GenConfig.sourceLb (259 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (259 : Fin 413)) := by
  change plane488GenSourceLb (259 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (259 : Fin 413)))
  rw [show plane488GenSourceLb (259 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (259 : Fin 413) = [384, 82, 50, 10, 6, 1] by decide]
  exact space2592_lower

theorem plane488_source0260 : plane488GenConfig.sourceLb (260 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (260 : Fin 413)) := by
  change plane488GenSourceLb (260 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (260 : Fin 413)))
  rw [show plane488GenSourceLb (260 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (260 : Fin 413) = [260, 149, 71, 39, 10] by decide]
  exact space3031_lower

theorem plane488_source0261 : plane488GenConfig.sourceLb (261 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (261 : Fin 413)) := by
  change plane488GenSourceLb (261 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (261 : Fin 413)))
  rw [show plane488GenSourceLb (261 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (261 : Fin 413) = [256, 131, 67, 35, 22, 10] by decide]
  exact space3032_lower

theorem plane488_source0262 : plane488GenConfig.sourceLb (262 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (262 : Fin 413)) := by
  change plane488GenSourceLb (262 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (262 : Fin 413)))
  rw [show plane488GenSourceLb (262 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (262 : Fin 413) = [258, 132, 71, 39, 23, 10] by decide]
  exact space3033_lower

theorem plane488_source0263 : plane488GenConfig.sourceLb (263 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (263 : Fin 413)) := by
  change plane488GenSourceLb (263 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (263 : Fin 413)))
  rw [show plane488GenSourceLb (263 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (263 : Fin 413) = [257, 130, 64, 32, 21, 10] by decide]
  exact space3034_lower

theorem plane488_source0264 : plane488GenConfig.sourceLb (264 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (264 : Fin 413)) := by
  change plane488GenSourceLb (264 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (264 : Fin 413)))
  rw [show plane488GenSourceLb (264 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (264 : Fin 413) = [256, 128, 70, 38, 16, 10] by decide]
  exact space3035_lower

theorem plane488_source0265 : plane488GenConfig.sourceLb (265 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (265 : Fin 413)) := by
  change plane488GenSourceLb (265 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (265 : Fin 413)))
  rw [show plane488GenSourceLb (265 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (265 : Fin 413) = [261, 130, 65, 33, 16, 10] by decide]
  exact space3036_lower

theorem plane488_source0266 : plane488GenConfig.sourceLb (266 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (266 : Fin 413)) := by
  change plane488GenSourceLb (266 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (266 : Fin 413)))
  rw [show plane488GenSourceLb (266 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (266 : Fin 413) = [288, 135, 96, 17, 10] by decide]
  exact space3037_lower

theorem plane488_source0267 : plane488GenConfig.sourceLb (267 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (267 : Fin 413)) := by
  change plane488GenSourceLb (267 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (267 : Fin 413)))
  rw [show plane488GenSourceLb (267 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (267 : Fin 413) = [259, 178, 96, 10, 7] by decide]
  exact space3038_lower

theorem plane488_source0268 : plane488GenConfig.sourceLb (268 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (268 : Fin 413)) := by
  change plane488GenSourceLb (268 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (268 : Fin 413)))
  rw [show plane488GenSourceLb (268 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (268 : Fin 413) = [274, 129, 66, 34, 10, 7] by decide]
  exact space3039_lower

theorem plane488_source0269 : plane488GenConfig.sourceLb (269 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (269 : Fin 413)) := by
  change plane488GenSourceLb (269 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (269 : Fin 413)))
  rw [show plane488GenSourceLb (269 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (269 : Fin 413) = [261, 128, 69, 37, 23, 10] by decide]
  exact space3040_lower

theorem plane488_source0270 : plane488GenConfig.sourceLb (270 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (270 : Fin 413)) := by
  change plane488GenSourceLb (270 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (270 : Fin 413)))
  rw [show plane488GenSourceLb (270 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (270 : Fin 413) = [262, 130, 65, 33, 18, 10] by decide]
  exact space3041_lower

theorem plane488_source0271 : plane488GenConfig.sourceLb (271 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (271 : Fin 413)) := by
  change plane488GenSourceLb (271 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (271 : Fin 413)))
  rw [show plane488GenSourceLb (271 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (271 : Fin 413) = [258, 128, 69, 37, 16, 10] by decide]
  exact space3042_lower

theorem plane488_source0272 : plane488GenConfig.sourceLb (272 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (272 : Fin 413)) := by
  change plane488GenSourceLb (272 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (272 : Fin 413)))
  rw [show plane488GenSourceLb (272 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (272 : Fin 413) = [262, 130, 67, 35, 16, 10] by decide]
  exact space3043_lower

theorem plane488_source0273 : plane488GenConfig.sourceLb (273 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (273 : Fin 413)) := by
  change plane488GenSourceLb (273 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (273 : Fin 413)))
  rw [show plane488GenSourceLb (273 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (273 : Fin 413) = [259, 147, 67, 35, 10, 4] by decide]
  exact space3044_lower

theorem plane488_source0274 : plane488GenConfig.sourceLb (274 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (274 : Fin 413)) := by
  change plane488GenSourceLb (274 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (274 : Fin 413)))
  rw [show plane488GenSourceLb (274 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (274 : Fin 413) = [385, 80, 48, 9, 5, 3] by decide]
  exact space3045_lower

theorem plane488_source0275 : plane488GenConfig.sourceLb (275 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (275 : Fin 413)) := by
  change plane488GenSourceLb (275 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (275 : Fin 413)))
  rw [show plane488GenSourceLb (275 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (275 : Fin 413) = [276, 128, 65, 33, 8, 2] by decide]
  exact space3046_lower

theorem plane488_source0276 : plane488GenConfig.sourceLb (276 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (276 : Fin 413)) := by
  change plane488GenSourceLb (276 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (276 : Fin 413)))
  rw [show plane488GenSourceLb (276 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (276 : Fin 413) = [385, 80, 48, 8, 4, 2] by decide]
  exact space2624_lower

theorem plane488_source0277 : plane488GenConfig.sourceLb (277 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (277 : Fin 413)) := by
  change plane488GenSourceLb (277 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (277 : Fin 413)))
  rw [show plane488GenSourceLb (277 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (277 : Fin 413) = [276, 134, 68, 36, 10, 1] by decide]
  exact space3047_lower

theorem plane488_source0278 : plane488GenConfig.sourceLb (278 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (278 : Fin 413)) := by
  change plane488GenSourceLb (278 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (278 : Fin 413)))
  rw [show plane488GenSourceLb (278 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (278 : Fin 413) = [386, 82, 50, 10, 6, 1] by decide]
  exact space2626_lower

theorem plane488_source0279 : plane488GenConfig.sourceLb (279 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (279 : Fin 413)) := by
  change plane488GenSourceLb (279 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (279 : Fin 413)))
  rw [show plane488GenSourceLb (279 : Fin 413) = 15 by decide,
      show plane488GenSourceBasis (279 : Fin 413) = [258, 176, 96, 10, 4, 1] by decide]
  exact space3048_lower

theorem plane488_source0280 : plane488GenConfig.sourceLb (280 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (280 : Fin 413)) := by
  change plane488GenSourceLb (280 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (280 : Fin 413)))
  rw [show plane488GenSourceLb (280 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (280 : Fin 413) = [259, 132, 64, 32, 22, 10] by decide]
  exact space3049_lower

theorem plane488_source0281 : plane488GenConfig.sourceLb (281 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (281 : Fin 413)) := by
  change plane488GenSourceLb (281 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (281 : Fin 413)))
  rw [show plane488GenSourceLb (281 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (281 : Fin 413) = [259, 129, 64, 32, 19, 10, 5] by decide]
  exact space1089_lower

theorem plane488_source0282 : plane488GenConfig.sourceLb (282 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (282 : Fin 413)) := by
  change plane488GenSourceLb (282 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (282 : Fin 413)))
  rw [show plane488GenSourceLb (282 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (282 : Fin 413) = [259, 128, 66, 34, 19, 10, 6] by decide]
  exact space1033_lower

theorem plane488_source0283 : plane488GenConfig.sourceLb (283 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (283 : Fin 413)) := by
  change plane488GenSourceLb (283 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (283 : Fin 413)))
  rw [show plane488GenSourceLb (283 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (283 : Fin 413) = [257, 129, 66, 34, 19, 10, 4] by decide]
  exact space0959_lower

theorem plane488_source0284 : plane488GenConfig.sourceLb (284 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (284 : Fin 413)) := by
  change plane488GenSourceLb (284 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (284 : Fin 413)))
  rw [show plane488GenSourceLb (284 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (284 : Fin 413) = [257, 128, 66, 34, 17, 10, 7] by decide]
  exact space2650_lower

theorem plane488_source0285 : plane488GenConfig.sourceLb (285 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (285 : Fin 413)) := by
  change plane488GenSourceLb (285 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (285 : Fin 413)))
  rw [show plane488GenSourceLb (285 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (285 : Fin 413) = [259, 128, 66, 34, 19, 10, 7] by decide]
  exact space0983_lower

theorem plane488_source0286 : plane488GenConfig.sourceLb (286 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (286 : Fin 413)) := by
  change plane488GenSourceLb (286 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (286 : Fin 413)))
  rw [show plane488GenSourceLb (286 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (286 : Fin 413) = [257, 130, 66, 34, 19, 10, 7] by decide]
  exact space0984_lower

theorem plane488_source0287 : plane488GenConfig.sourceLb (287 : Fin 413) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (287 : Fin 413)) := by
  change plane488GenSourceLb (287 : Fin 413) ≤
    frozenWangTable.L0 (spanCodes (plane488GenSourceBasis (287 : Fin 413)))
  rw [show plane488GenSourceLb (287 : Fin 413) = 14 by decide,
      show plane488GenSourceBasis (287 : Fin 413) = [259, 129, 66, 34, 19, 10, 6] by decide]
  exact space0976_lower

theorem plane488_sourceBlock008 (offset : Fin 32)
    (hlt : 8 * 32 + offset.val < 413) :
    plane488GenConfig.sourceLb (Fin.mk (8 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane488GenConfig.sourceU (Fin.mk (8 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane488_source0256
  | ⟨1, _⟩ => intro hlt; exact plane488_source0257
  | ⟨2, _⟩ => intro hlt; exact plane488_source0258
  | ⟨3, _⟩ => intro hlt; exact plane488_source0259
  | ⟨4, _⟩ => intro hlt; exact plane488_source0260
  | ⟨5, _⟩ => intro hlt; exact plane488_source0261
  | ⟨6, _⟩ => intro hlt; exact plane488_source0262
  | ⟨7, _⟩ => intro hlt; exact plane488_source0263
  | ⟨8, _⟩ => intro hlt; exact plane488_source0264
  | ⟨9, _⟩ => intro hlt; exact plane488_source0265
  | ⟨10, _⟩ => intro hlt; exact plane488_source0266
  | ⟨11, _⟩ => intro hlt; exact plane488_source0267
  | ⟨12, _⟩ => intro hlt; exact plane488_source0268
  | ⟨13, _⟩ => intro hlt; exact plane488_source0269
  | ⟨14, _⟩ => intro hlt; exact plane488_source0270
  | ⟨15, _⟩ => intro hlt; exact plane488_source0271
  | ⟨16, _⟩ => intro hlt; exact plane488_source0272
  | ⟨17, _⟩ => intro hlt; exact plane488_source0273
  | ⟨18, _⟩ => intro hlt; exact plane488_source0274
  | ⟨19, _⟩ => intro hlt; exact plane488_source0275
  | ⟨20, _⟩ => intro hlt; exact plane488_source0276
  | ⟨21, _⟩ => intro hlt; exact plane488_source0277
  | ⟨22, _⟩ => intro hlt; exact plane488_source0278
  | ⟨23, _⟩ => intro hlt; exact plane488_source0279
  | ⟨24, _⟩ => intro hlt; exact plane488_source0280
  | ⟨25, _⟩ => intro hlt; exact plane488_source0281
  | ⟨26, _⟩ => intro hlt; exact plane488_source0282
  | ⟨27, _⟩ => intro hlt; exact plane488_source0283
  | ⟨28, _⟩ => intro hlt; exact plane488_source0284
  | ⟨29, _⟩ => intro hlt; exact plane488_source0285
  | ⟨30, _⟩ => intro hlt; exact plane488_source0286
  | ⟨31, _⟩ => intro hlt; exact plane488_source0287
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
