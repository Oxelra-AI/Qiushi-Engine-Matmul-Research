import QiushiPlane485GenData
import QiushiFrozenWangSpaces021
import QiushiFrozenWangSpaces022
import QiushiFrozenWangSpaces024
import QiushiFrozenWangSpaces026
import QiushiFrozenWangSpaces059
import QiushiFrozenWangSpaces060

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane485_source0256 : plane485GenConfig.sourceLb (256 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (256 : Fin 421)) := by
  change plane485GenSourceLb (256 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (256 : Fin 421)))
  rw [show plane485GenSourceLb (256 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (256 : Fin 421) = [291, 160, 97, 19, 10, 7] by decide]
  exact space0701_lower

theorem plane485_source0257 : plane485GenConfig.sourceLb (257 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (257 : Fin 421)) := by
  change plane485GenSourceLb (257 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (257 : Fin 421)))
  rw [show plane485GenSourceLb (257 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (257 : Fin 421) = [288, 134, 66, 20, 10, 1] by decide]
  exact space1912_lower

theorem plane485_source0258 : plane485GenConfig.sourceLb (258 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (258 : Fin 421)) := by
  change plane485GenSourceLb (258 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (258 : Fin 421)))
  rw [show plane485GenSourceLb (258 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (258 : Fin 421) = [450, 32, 18, 10, 6, 1] by decide]
  exact space0708_lower

theorem plane485_source0259 : plane485GenConfig.sourceLb (259 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (259 : Fin 421)) := by
  change plane485GenSourceLb (259 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (259 : Fin 421)))
  rw [show plane485GenSourceLb (259 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (259 : Fin 421) = [261, 197, 38, 20, 10] by decide]
  exact space1913_lower

theorem plane485_source0260 : plane485GenConfig.sourceLb (260 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (260 : Fin 421)) := by
  change plane485GenSourceLb (260 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (260 : Fin 421)))
  rw [show plane485GenSourceLb (260 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (260 : Fin 421) = [259, 195, 38, 20, 10] by decide]
  exact space1914_lower

theorem plane485_source0261 : plane485GenConfig.sourceLb (261 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (261 : Fin 421)) := by
  change plane485GenSourceLb (261 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (261 : Fin 421)))
  rw [show plane485GenSourceLb (261 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (261 : Fin 421) = [387, 67, 38, 20, 10] by decide]
  exact space1915_lower

theorem plane485_source0262 : plane485GenConfig.sourceLb (262 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (262 : Fin 421)) := by
  change plane485GenSourceLb (262 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (262 : Fin 421)))
  rw [show plane485GenSourceLb (262 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (262 : Fin 421) = [258, 132, 71, 39, 20, 10] by decide]
  exact space1916_lower

theorem plane485_source0263 : plane485GenConfig.sourceLb (263 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (263 : Fin 421)) := by
  change plane485GenSourceLb (263 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (263 : Fin 421)))
  rw [show plane485GenSourceLb (263 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (263 : Fin 421) = [259, 129, 64, 36, 20, 10] by decide]
  exact space1917_lower

theorem plane485_source0264 : plane485GenConfig.sourceLb (264 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (264 : Fin 421)) := by
  change plane485GenSourceLb (264 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (264 : Fin 421)))
  rw [show plane485GenSourceLb (264 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (264 : Fin 421) = [262, 131, 65, 34, 20, 10] by decide]
  exact space1918_lower

theorem plane485_source0265 : plane485GenConfig.sourceLb (265 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (265 : Fin 421)) := by
  change plane485GenSourceLb (265 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (265 : Fin 421)))
  rw [show plane485GenSourceLb (265 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (265 : Fin 421) = [256, 128, 70, 32, 20, 10] by decide]
  exact space1919_lower

theorem plane485_source0266 : plane485GenConfig.sourceLb (266 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (266 : Fin 421)) := by
  change plane485GenSourceLb (266 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (266 : Fin 421)))
  rw [show plane485GenSourceLb (266 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (266 : Fin 421) = [262, 131, 67, 32, 20, 10] by decide]
  exact space1920_lower

theorem plane485_source0267 : plane485GenConfig.sourceLb (267 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (267 : Fin 421)) := by
  change plane485GenSourceLb (267 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (267 : Fin 421)))
  rw [show plane485GenSourceLb (267 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (267 : Fin 421) = [262, 129, 65, 32, 20, 10] by decide]
  exact space1921_lower

theorem plane485_source0268 : plane485GenConfig.sourceLb (268 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (268 : Fin 421)) := by
  change plane485GenSourceLb (268 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (268 : Fin 421)))
  rw [show plane485GenSourceLb (268 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (268 : Fin 421) = [261, 194, 33, 20, 10] by decide]
  exact space1922_lower

theorem plane485_source0269 : plane485GenConfig.sourceLb (269 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (269 : Fin 421)) := by
  change plane485GenSourceLb (269 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (269 : Fin 421)))
  rw [show plane485GenSourceLb (269 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (269 : Fin 421) = [256, 225, 19, 10, 7] by decide]
  exact space0797_lower

theorem plane485_source0270 : plane485GenConfig.sourceLb (270 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (270 : Fin 421)) := by
  change plane485GenSourceLb (270 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (270 : Fin 421)))
  rw [show plane485GenSourceLb (270 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (270 : Fin 421) = [320, 161, 19, 10, 7] by decide]
  exact space0798_lower

theorem plane485_source0271 : plane485GenConfig.sourceLb (271 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (271 : Fin 421)) := by
  change plane485GenSourceLb (271 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (271 : Fin 421)))
  rw [show plane485GenSourceLb (271 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (271 : Fin 421) = [291, 162, 99, 16, 10, 4] by decide]
  exact space1923_lower

theorem plane485_source0272 : plane485GenConfig.sourceLb (272 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (272 : Fin 421)) := by
  change plane485GenSourceLb (272 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (272 : Fin 421)))
  rw [show plane485GenSourceLb (272 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (272 : Fin 421) = [257, 162, 65, 16, 10, 4] by decide]
  exact space1924_lower

theorem plane485_source0273 : plane485GenConfig.sourceLb (273 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (273 : Fin 421)) := by
  change plane485GenSourceLb (273 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (273 : Fin 421)))
  rw [show plane485GenSourceLb (273 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (273 : Fin 421) = [257, 162, 64, 17, 10, 5] by decide]
  exact space1925_lower

theorem plane485_source0274 : plane485GenConfig.sourceLb (274 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (274 : Fin 421)) := by
  change plane485GenSourceLb (274 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (274 : Fin 421)))
  rw [show plane485GenSourceLb (274 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (274 : Fin 421) = [260, 129, 97, 20, 8, 2] by decide]
  exact space1926_lower

theorem plane485_source0275 : plane485GenConfig.sourceLb (275 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (275 : Fin 421)) := by
  change plane485GenSourceLb (275 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (275 : Fin 421)))
  rw [show plane485GenSourceLb (275 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (275 : Fin 421) = [292, 165, 100, 20, 9, 3] by decide]
  exact space1927_lower

theorem plane485_source0276 : plane485GenConfig.sourceLb (276 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (276 : Fin 421)) := by
  change plane485GenSourceLb (276 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (276 : Fin 421)))
  rw [show plane485GenSourceLb (276 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (276 : Fin 421) = [261, 128, 69, 39, 20, 10] by decide]
  exact space1928_lower

theorem plane485_source0277 : plane485GenConfig.sourceLb (277 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (277 : Fin 421)) := by
  change plane485GenSourceLb (277 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (277 : Fin 421)))
  rw [show plane485GenSourceLb (277 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (277 : Fin 421) = [263, 134, 65, 39, 20, 10] by decide]
  exact space1929_lower

theorem plane485_source0278 : plane485GenConfig.sourceLb (278 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (278 : Fin 421)) := by
  change plane485GenSourceLb (278 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (278 : Fin 421)))
  rw [show plane485GenSourceLb (278 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (278 : Fin 421) = [260, 130, 69, 36, 20, 10] by decide]
  exact space1930_lower

theorem plane485_source0279 : plane485GenConfig.sourceLb (279 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (279 : Fin 421)) := by
  change plane485GenSourceLb (279 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (279 : Fin 421)))
  rw [show plane485GenSourceLb (279 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (279 : Fin 421) = [260, 134, 69, 32, 20, 10] by decide]
  exact space1931_lower

theorem plane485_source0280 : plane485GenConfig.sourceLb (280 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (280 : Fin 421)) := by
  change plane485GenSourceLb (280 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (280 : Fin 421)))
  rw [show plane485GenSourceLb (280 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (280 : Fin 421) = [258, 135, 66, 32, 20, 10] by decide]
  exact space1932_lower

theorem plane485_source0281 : plane485GenConfig.sourceLb (281 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (281 : Fin 421)) := by
  change plane485GenSourceLb (281 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (281 : Fin 421)))
  rw [show plane485GenSourceLb (281 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (281 : Fin 421) = [290, 162, 98, 17, 10, 5] by decide]
  exact space1933_lower

theorem plane485_source0282 : plane485GenConfig.sourceLb (282 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (282 : Fin 421)) := by
  change plane485GenSourceLb (282 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (282 : Fin 421)))
  rw [show plane485GenSourceLb (282 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (282 : Fin 421) = [289, 132, 65, 20, 9, 3] by decide]
  exact space1934_lower

theorem plane485_source0283 : plane485GenConfig.sourceLb (283 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (283 : Fin 421)) := by
  change plane485GenSourceLb (283 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (283 : Fin 421)))
  rw [show plane485GenSourceLb (283 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (283 : Fin 421) = [449, 33, 16, 9, 4, 3] by decide]
  exact space0859_lower

theorem plane485_source0284 : plane485GenConfig.sourceLb (284 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (284 : Fin 421)) := by
  change plane485GenSourceLb (284 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (284 : Fin 421)))
  rw [show plane485GenSourceLb (284 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (284 : Fin 421) = [289, 132, 64, 20, 8, 2] by decide]
  exact space1935_lower

theorem plane485_source0285 : plane485GenConfig.sourceLb (285 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (285 : Fin 421)) := by
  change plane485GenSourceLb (285 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (285 : Fin 421)))
  rw [show plane485GenSourceLb (285 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (285 : Fin 421) = [449, 33, 17, 8, 5, 2] by decide]
  exact space0861_lower

theorem plane485_source0286 : plane485GenConfig.sourceLb (286 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (286 : Fin 421)) := by
  change plane485GenSourceLb (286 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (286 : Fin 421)))
  rw [show plane485GenSourceLb (286 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (286 : Fin 421) = [260, 166, 68, 20, 10, 1] by decide]
  exact space1936_lower

theorem plane485_source0287 : plane485GenConfig.sourceLb (287 : Fin 421) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (287 : Fin 421)) := by
  change plane485GenSourceLb (287 : Fin 421) ≤
    frozenWangTable.L0 (spanCodes (plane485GenSourceBasis (287 : Fin 421)))
  rw [show plane485GenSourceLb (287 : Fin 421) = 15 by decide,
      show plane485GenSourceBasis (287 : Fin 421) = [290, 134, 66, 20, 10, 1] by decide]
  exact space1937_lower

theorem plane485_sourceBlock008 (offset : Fin 32)
    (hlt : 8 * 32 + offset.val < 421) :
    plane485GenConfig.sourceLb (Fin.mk (8 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane485GenConfig.sourceU (Fin.mk (8 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane485_source0256
  | ⟨1, _⟩ => intro hlt; exact plane485_source0257
  | ⟨2, _⟩ => intro hlt; exact plane485_source0258
  | ⟨3, _⟩ => intro hlt; exact plane485_source0259
  | ⟨4, _⟩ => intro hlt; exact plane485_source0260
  | ⟨5, _⟩ => intro hlt; exact plane485_source0261
  | ⟨6, _⟩ => intro hlt; exact plane485_source0262
  | ⟨7, _⟩ => intro hlt; exact plane485_source0263
  | ⟨8, _⟩ => intro hlt; exact plane485_source0264
  | ⟨9, _⟩ => intro hlt; exact plane485_source0265
  | ⟨10, _⟩ => intro hlt; exact plane485_source0266
  | ⟨11, _⟩ => intro hlt; exact plane485_source0267
  | ⟨12, _⟩ => intro hlt; exact plane485_source0268
  | ⟨13, _⟩ => intro hlt; exact plane485_source0269
  | ⟨14, _⟩ => intro hlt; exact plane485_source0270
  | ⟨15, _⟩ => intro hlt; exact plane485_source0271
  | ⟨16, _⟩ => intro hlt; exact plane485_source0272
  | ⟨17, _⟩ => intro hlt; exact plane485_source0273
  | ⟨18, _⟩ => intro hlt; exact plane485_source0274
  | ⟨19, _⟩ => intro hlt; exact plane485_source0275
  | ⟨20, _⟩ => intro hlt; exact plane485_source0276
  | ⟨21, _⟩ => intro hlt; exact plane485_source0277
  | ⟨22, _⟩ => intro hlt; exact plane485_source0278
  | ⟨23, _⟩ => intro hlt; exact plane485_source0279
  | ⟨24, _⟩ => intro hlt; exact plane485_source0280
  | ⟨25, _⟩ => intro hlt; exact plane485_source0281
  | ⟨26, _⟩ => intro hlt; exact plane485_source0282
  | ⟨27, _⟩ => intro hlt; exact plane485_source0283
  | ⟨28, _⟩ => intro hlt; exact plane485_source0284
  | ⟨29, _⟩ => intro hlt; exact plane485_source0285
  | ⟨30, _⟩ => intro hlt; exact plane485_source0286
  | ⟨31, _⟩ => intro hlt; exact plane485_source0287
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
