import QiushiPlane490GenData
import QiushiFrozenWangSpaces009
import QiushiFrozenWangSpaces010
import QiushiFrozenWangSpaces011
import QiushiFrozenWangSpaces057
import QiushiFrozenWangSpaces058
import QiushiFrozenWangSpaces078
import QiushiFrozenWangSpaces113
import QiushiFrozenWangSpaces114

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane490_source0256 : plane490GenConfig.sourceLb (256 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (256 : Fin 713)) := by
  change plane490GenSourceLb (256 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (256 : Fin 713)))
  rw [show plane490GenSourceLb (256 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (256 : Fin 713) = [256, 165, 101, 19, 10] by decide]
  exact space0317_lower

theorem plane490_source0257 : plane490GenConfig.sourceLb (257 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (257 : Fin 713)) := by
  change plane490GenSourceLb (257 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (257 : Fin 713)))
  rw [show plane490GenSourceLb (257 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (257 : Fin 713) = [260, 165, 97, 20, 9, 3] by decide]
  exact space3629_lower

theorem plane490_source0258 : plane490GenConfig.sourceLb (258 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (258 : Fin 713)) := by
  change plane490GenSourceLb (258 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (258 : Fin 713)))
  rw [show plane490GenSourceLb (258 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (258 : Fin 713) = [260, 161, 101, 20, 9, 3] by decide]
  exact space1844_lower

theorem plane490_source0259 : plane490GenConfig.sourceLb (259 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (259 : Fin 713)) := by
  change plane490GenSourceLb (259 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (259 : Fin 713)))
  rw [show plane490GenSourceLb (259 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (259 : Fin 713) = [256, 134, 64, 19, 10] by decide]
  exact space0367_lower

theorem plane490_source0260 : plane490GenConfig.sourceLb (260 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (260 : Fin 713)) := by
  change plane490GenSourceLb (260 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (260 : Fin 713)))
  rw [show plane490GenSourceLb (260 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (260 : Fin 713) = [262, 128, 64, 20, 10, 1] by decide]
  exact space1863_lower

theorem plane490_source0261 : plane490GenConfig.sourceLb (261 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (261 : Fin 713)) := by
  change plane490GenSourceLb (261 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (261 : Fin 713)))
  rw [show plane490GenSourceLb (261 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (261 : Fin 713) = [256, 128, 69, 19, 10] by decide]
  exact space0349_lower

theorem plane490_source0262 : plane490GenConfig.sourceLb (262 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (262 : Fin 713)) := by
  change plane490GenSourceLb (262 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (262 : Fin 713)))
  rw [show plane490GenSourceLb (262 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (262 : Fin 713) = [275, 144, 65, 10, 7] by decide]
  exact space3630_lower

theorem plane490_source0263 : plane490GenConfig.sourceLb (263 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (263 : Fin 713)) := by
  change plane490GenSourceLb (263 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (263 : Fin 713)))
  rw [show plane490GenSourceLb (263 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (263 : Fin 713) = [261, 129, 65, 21, 9, 3] by decide]
  exact space2503_lower

theorem plane490_source0264 : plane490GenConfig.sourceLb (264 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (264 : Fin 713)) := by
  change plane490GenSourceLb (264 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (264 : Fin 713)))
  rw [show plane490GenSourceLb (264 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (264 : Fin 713) = [256, 160, 98, 19, 10, 6] by decide]
  exact space0343_lower

theorem plane490_source0265 : plane490GenConfig.sourceLb (265 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (265 : Fin 713)) := by
  change plane490GenSourceLb (265 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (265 : Fin 713)))
  rw [show plane490GenSourceLb (265 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (265 : Fin 713) = [256, 160, 97, 19, 10, 5] by decide]
  exact space0342_lower

theorem plane490_source0266 : plane490GenConfig.sourceLb (266 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (266 : Fin 713)) := by
  change plane490GenSourceLb (266 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (266 : Fin 713)))
  rw [show plane490GenSourceLb (266 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (266 : Fin 713) = [258, 163, 96, 17, 10, 5] by decide]
  exact space1848_lower

theorem plane490_source0267 : plane490GenConfig.sourceLb (267 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (267 : Fin 713)) := by
  change plane490GenSourceLb (267 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (267 : Fin 713)))
  rw [show plane490GenSourceLb (267 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (267 : Fin 713) = [261, 128, 65, 20, 8, 2] by decide]
  exact space1852_lower

theorem plane490_source0268 : plane490GenConfig.sourceLb (268 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (268 : Fin 713)) := by
  change plane490GenSourceLb (268 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (268 : Fin 713)))
  rw [show plane490GenSourceLb (268 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (268 : Fin 713) = [260, 128, 64, 22, 10, 1] by decide]
  exact space3631_lower

theorem plane490_source0269 : plane490GenConfig.sourceLb (269 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (269 : Fin 713)) := by
  change plane490GenSourceLb (269 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (269 : Fin 713)))
  rw [show plane490GenSourceLb (269 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (269 : Fin 713) = [274, 162, 114, 10, 6, 1] by decide]
  exact space3632_lower

theorem plane490_source0270 : plane490GenConfig.sourceLb (270 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (270 : Fin 713)) := by
  change plane490GenSourceLb (270 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (270 : Fin 713)))
  rw [show plane490GenSourceLb (270 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (270 : Fin 713) = [275, 128, 83, 51, 10] by decide]
  exact space3633_lower

theorem plane490_source0271 : plane490GenConfig.sourceLb (271 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (271 : Fin 713)) := by
  change plane490GenSourceLb (271 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (271 : Fin 713)))
  rw [show plane490GenSourceLb (271 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (271 : Fin 713) = [274, 150, 66, 52, 10, 1] by decide]
  exact space3634_lower

theorem plane490_source0272 : plane490GenConfig.sourceLb (272 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (272 : Fin 713)) := by
  change plane490GenSourceLb (272 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (272 : Fin 713)))
  rw [show plane490GenSourceLb (272 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (272 : Fin 713) = [272, 133, 80, 52, 9, 3] by decide]
  exact space3635_lower

theorem plane490_source0273 : plane490GenConfig.sourceLb (273 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (273 : Fin 713)) := by
  change plane490GenSourceLb (273 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (273 : Fin 713)))
  rw [show plane490GenSourceLb (273 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (273 : Fin 713) = [275, 144, 65, 50, 10] by decide]
  exact space3636_lower

theorem plane490_source0274 : plane490GenConfig.sourceLb (274 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (274 : Fin 713)) := by
  change plane490GenSourceLb (274 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (274 : Fin 713)))
  rw [show plane490GenSourceLb (274 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (274 : Fin 713) = [275, 147, 80, 33, 10, 6] by decide]
  exact space3637_lower

theorem plane490_source0275 : plane490GenConfig.sourceLb (275 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (275 : Fin 713)) := by
  change plane490GenSourceLb (275 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (275 : Fin 713)))
  rw [show plane490GenSourceLb (275 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (275 : Fin 713) = [275, 145, 66, 49, 10, 6] by decide]
  exact space3638_lower

theorem plane490_source0276 : plane490GenConfig.sourceLb (276 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (276 : Fin 713)) := by
  change plane490GenSourceLb (276 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (276 : Fin 713)))
  rw [show plane490GenSourceLb (276 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (276 : Fin 713) = [275, 131, 80, 49, 10, 6] by decide]
  exact space3639_lower

theorem plane490_source0277 : plane490GenConfig.sourceLb (277 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (277 : Fin 713)) := by
  change plane490GenSourceLb (277 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (277 : Fin 713)))
  rw [show plane490GenSourceLb (277 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (277 : Fin 713) = [275, 130, 81, 51, 10, 5] by decide]
  exact space3640_lower

theorem plane490_source0278 : plane490GenConfig.sourceLb (278 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (278 : Fin 713)) := by
  change plane490GenSourceLb (278 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (278 : Fin 713)))
  rw [show plane490GenSourceLb (278 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (278 : Fin 713) = [275, 130, 80, 48, 10, 7] by decide]
  exact space3641_lower

theorem plane490_source0279 : plane490GenConfig.sourceLb (279 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (279 : Fin 713)) := by
  change plane490GenSourceLb (279 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (279 : Fin 713)))
  rw [show plane490GenSourceLb (279 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (279 : Fin 713) = [275, 129, 83, 48, 10, 7] by decide]
  exact space2523_lower

theorem plane490_source0280 : plane490GenConfig.sourceLb (280 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (280 : Fin 713)) := by
  change plane490GenSourceLb (280 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (280 : Fin 713)))
  rw [show plane490GenSourceLb (280 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (280 : Fin 713) = [275, 130, 83, 51, 10, 7] by decide]
  exact space3642_lower

theorem plane490_source0281 : plane490GenConfig.sourceLb (281 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (281 : Fin 713)) := by
  change plane490GenSourceLb (281 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (281 : Fin 713)))
  rw [show plane490GenSourceLb (281 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (281 : Fin 713) = [274, 162, 66, 10, 4, 1] by decide]
  exact space3643_lower

theorem plane490_source0282 : plane490GenConfig.sourceLb (282 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (282 : Fin 713)) := by
  change plane490GenSourceLb (282 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (282 : Fin 713)))
  rw [show plane490GenSourceLb (282 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (282 : Fin 713) = [274, 162, 64, 10, 6, 1] by decide]
  exact space3644_lower

theorem plane490_source0283 : plane490GenConfig.sourceLb (283 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (283 : Fin 713)) := by
  change plane490GenSourceLb (283 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (283 : Fin 713)))
  rw [show plane490GenSourceLb (283 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (283 : Fin 713) = [275, 145, 67, 51, 10, 7] by decide]
  exact space3645_lower

theorem plane490_source0284 : plane490GenConfig.sourceLb (284 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (284 : Fin 713)) := by
  change plane490GenSourceLb (284 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (284 : Fin 713)))
  rw [show plane490GenSourceLb (284 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (284 : Fin 713) = [275, 147, 67, 49, 10, 7] by decide]
  exact space3646_lower

theorem plane490_source0285 : plane490GenConfig.sourceLb (285 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (285 : Fin 713)) := by
  change plane490GenSourceLb (285 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (285 : Fin 713)))
  rw [show plane490GenSourceLb (285 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (285 : Fin 713) = [275, 129, 83, 48, 10, 4] by decide]
  exact space3647_lower

theorem plane490_source0286 : plane490GenConfig.sourceLb (286 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (286 : Fin 713)) := by
  change plane490GenSourceLb (286 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (286 : Fin 713)))
  rw [show plane490GenSourceLb (286 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (286 : Fin 713) = [275, 147, 80, 32, 10, 5] by decide]
  exact space3648_lower

theorem plane490_source0287 : plane490GenConfig.sourceLb (287 : Fin 713) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (287 : Fin 713)) := by
  change plane490GenSourceLb (287 : Fin 713) ≤
    frozenWangTable.L0 (spanCodes (plane490GenSourceBasis (287 : Fin 713)))
  rw [show plane490GenSourceLb (287 : Fin 713) = 15 by decide,
      show plane490GenSourceBasis (287 : Fin 713) = [275, 144, 82, 33, 10, 5] by decide]
  exact space3649_lower

theorem plane490_sourceBlock008 (offset : Fin 32)
    (hlt : 8 * 32 + offset.val < 713) :
    plane490GenConfig.sourceLb (Fin.mk (8 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane490GenConfig.sourceU (Fin.mk (8 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane490_source0256
  | ⟨1, _⟩ => intro hlt; exact plane490_source0257
  | ⟨2, _⟩ => intro hlt; exact plane490_source0258
  | ⟨3, _⟩ => intro hlt; exact plane490_source0259
  | ⟨4, _⟩ => intro hlt; exact plane490_source0260
  | ⟨5, _⟩ => intro hlt; exact plane490_source0261
  | ⟨6, _⟩ => intro hlt; exact plane490_source0262
  | ⟨7, _⟩ => intro hlt; exact plane490_source0263
  | ⟨8, _⟩ => intro hlt; exact plane490_source0264
  | ⟨9, _⟩ => intro hlt; exact plane490_source0265
  | ⟨10, _⟩ => intro hlt; exact plane490_source0266
  | ⟨11, _⟩ => intro hlt; exact plane490_source0267
  | ⟨12, _⟩ => intro hlt; exact plane490_source0268
  | ⟨13, _⟩ => intro hlt; exact plane490_source0269
  | ⟨14, _⟩ => intro hlt; exact plane490_source0270
  | ⟨15, _⟩ => intro hlt; exact plane490_source0271
  | ⟨16, _⟩ => intro hlt; exact plane490_source0272
  | ⟨17, _⟩ => intro hlt; exact plane490_source0273
  | ⟨18, _⟩ => intro hlt; exact plane490_source0274
  | ⟨19, _⟩ => intro hlt; exact plane490_source0275
  | ⟨20, _⟩ => intro hlt; exact plane490_source0276
  | ⟨21, _⟩ => intro hlt; exact plane490_source0277
  | ⟨22, _⟩ => intro hlt; exact plane490_source0278
  | ⟨23, _⟩ => intro hlt; exact plane490_source0279
  | ⟨24, _⟩ => intro hlt; exact plane490_source0280
  | ⟨25, _⟩ => intro hlt; exact plane490_source0281
  | ⟨26, _⟩ => intro hlt; exact plane490_source0282
  | ⟨27, _⟩ => intro hlt; exact plane490_source0283
  | ⟨28, _⟩ => intro hlt; exact plane490_source0284
  | ⟨29, _⟩ => intro hlt; exact plane490_source0285
  | ⟨30, _⟩ => intro hlt; exact plane490_source0286
  | ⟨31, _⟩ => intro hlt; exact plane490_source0287
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
