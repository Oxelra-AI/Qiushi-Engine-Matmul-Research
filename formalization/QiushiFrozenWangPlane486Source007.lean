import QiushiPlane486GenData
import QiushiFrozenWangSpaces036
import QiushiFrozenWangSpaces037
import QiushiFrozenWangSpaces050
import QiushiFrozenWangSpaces051
import QiushiFrozenWangSpaces062
import QiushiFrozenWangSpaces069
import QiushiFrozenWangSpaces070

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem plane486_source0224 : plane486GenConfig.sourceLb (224 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (224 : Fin 262)) := by
  change plane486GenSourceLb (224 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (224 : Fin 262)))
  rw [show plane486GenSourceLb (224 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (224 : Fin 262) = [258, 128, 64, 32, 16, 10, 4] by decide]
  exact space2238_lower

theorem plane486_source0225 : plane486GenConfig.sourceLb (225 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (225 : Fin 262)) := by
  change plane486GenSourceLb (225 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (225 : Fin 262)))
  rw [show plane486GenSourceLb (225 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (225 : Fin 262) = [259, 128, 64, 32, 17, 10, 4] by decide]
  exact space2239_lower

theorem plane486_source0226 : plane486GenConfig.sourceLb (226 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (226 : Fin 262)) := by
  change plane486GenSourceLb (226 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (226 : Fin 262)))
  rw [show plane486GenSourceLb (226 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (226 : Fin 262) = [256, 129, 65, 32, 18, 10, 5] by decide]
  exact space2240_lower

theorem plane486_source0227 : plane486GenConfig.sourceLb (227 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (227 : Fin 262)) := by
  change plane486GenSourceLb (227 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (227 : Fin 262)))
  rw [show plane486GenSourceLb (227 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (227 : Fin 262) = [256, 128, 65, 33, 18, 10, 5] by decide]
  exact space2241_lower

theorem plane486_source0228 : plane486GenConfig.sourceLb (228 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (228 : Fin 262)) := by
  change plane486GenSourceLb (228 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (228 : Fin 262)))
  rw [show plane486GenSourceLb (228 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (228 : Fin 262) = [259, 130, 65, 34, 16, 10, 5] by decide]
  exact space2242_lower

theorem plane486_source0229 : plane486GenConfig.sourceLb (229 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (229 : Fin 262)) := by
  change plane486GenSourceLb (229 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (229 : Fin 262)))
  rw [show plane486GenSourceLb (229 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (229 : Fin 262) = [256, 128, 68, 32, 20, 8, 2] by decide]
  exact space2243_lower

theorem plane486_source0230 : plane486GenConfig.sourceLb (230 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (230 : Fin 262)) := by
  change plane486GenSourceLb (230 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (230 : Fin 262)))
  rw [show plane486GenSourceLb (230 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (230 : Fin 262) = [257, 128, 68, 32, 21, 8, 2] by decide]
  exact space2244_lower

theorem plane486_source0231 : plane486GenConfig.sourceLb (231 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (231 : Fin 262)) := by
  change plane486GenSourceLb (231 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (231 : Fin 262)))
  rw [show plane486GenSourceLb (231 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (231 : Fin 262) = [260, 133, 68, 36, 17, 8, 2] by decide]
  exact space1215_lower

theorem plane486_source0232 : plane486GenConfig.sourceLb (232 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (232 : Fin 262)) := by
  change plane486GenSourceLb (232 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (232 : Fin 262)))
  rw [show plane486GenSourceLb (232 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (232 : Fin 262) = [260, 132, 68, 37, 17, 8, 2] by decide]
  exact space1213_lower

theorem plane486_source0233 : plane486GenConfig.sourceLb (233 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (233 : Fin 262)) := by
  change plane486GenSourceLb (233 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (233 : Fin 262)))
  rw [show plane486GenSourceLb (233 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (233 : Fin 262) = [257, 132, 68, 36, 20, 9, 3] by decide]
  exact space2245_lower

theorem plane486_source0234 : plane486GenConfig.sourceLb (234 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (234 : Fin 262)) := by
  change plane486GenSourceLb (234 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (234 : Fin 262)))
  rw [show plane486GenSourceLb (234 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (234 : Fin 262) = [256, 132, 68, 36, 21, 9, 3] by decide]
  exact space2246_lower

theorem plane486_source0235 : plane486GenConfig.sourceLb (235 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (235 : Fin 262)) := by
  change plane486GenSourceLb (235 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (235 : Fin 262)))
  rw [show plane486GenSourceLb (235 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (235 : Fin 262) = [260, 129, 68, 32, 16, 9, 3] by decide]
  exact space1183_lower

theorem plane486_source0236 : plane486GenConfig.sourceLb (236 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (236 : Fin 262)) := by
  change plane486GenSourceLb (236 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (236 : Fin 262)))
  rw [show plane486GenSourceLb (236 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (236 : Fin 262) = [260, 128, 68, 33, 16, 9, 3] by decide]
  exact space1186_lower

theorem plane486_source0237 : plane486GenConfig.sourceLb (237 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (237 : Fin 262)) := by
  change plane486GenSourceLb (237 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (237 : Fin 262)))
  rw [show plane486GenSourceLb (237 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (237 : Fin 262) = [259, 130, 67, 35, 18, 10, 7] by decide]
  exact space2247_lower

theorem plane486_source0238 : plane486GenConfig.sourceLb (238 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (238 : Fin 262)) := by
  change plane486GenSourceLb (238 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (238 : Fin 262)))
  rw [show plane486GenSourceLb (238 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (238 : Fin 262) = [259, 131, 67, 34, 18, 10, 7] by decide]
  exact space2248_lower

theorem plane486_source0239 : plane486GenConfig.sourceLb (239 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (239 : Fin 262)) := by
  change plane486GenSourceLb (239 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (239 : Fin 262)))
  rw [show plane486GenSourceLb (239 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (239 : Fin 262) = [258, 128, 66, 33, 18, 10, 6] by decide]
  exact space1996_lower

theorem plane486_source0240 : plane486GenConfig.sourceLb (240 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (240 : Fin 262)) := by
  change plane486GenSourceLb (240 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (240 : Fin 262)))
  rw [show plane486GenSourceLb (240 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (240 : Fin 262) = [258, 129, 66, 32, 18, 10, 6] by decide]
  exact space1998_lower

theorem plane486_source0241 : plane486GenConfig.sourceLb (241 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (241 : Fin 262)) := by
  change plane486GenSourceLb (241 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (241 : Fin 262)))
  rw [show plane486GenSourceLb (241 : Fin 262) = 12 by decide,
      show plane486GenSourceBasis (241 : Fin 262) = [272, 128, 66, 32, 10, 6, 1] by decide]
  exact space2249_lower

theorem plane486_source0242 : plane486GenConfig.sourceLb (242 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (242 : Fin 262)) := by
  change plane486GenSourceLb (242 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (242 : Fin 262)))
  rw [show plane486GenSourceLb (242 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (242 : Fin 262) = [256, 128, 66, 32, 18, 10, 6, 1] by decide]
  exact space1623_lower

theorem plane486_source0243 : plane486GenConfig.sourceLb (243 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (243 : Fin 262)) := by
  change plane486GenSourceLb (243 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (243 : Fin 262)))
  rw [show plane486GenSourceLb (243 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (243 : Fin 262) = [258, 128, 66, 34, 18, 10, 6, 1] by decide]
  exact space1625_lower

theorem plane486_source0244 : plane486GenConfig.sourceLb (244 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (244 : Fin 262)) := by
  change plane486GenSourceLb (244 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (244 : Fin 262)))
  rw [show plane486GenSourceLb (244 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (244 : Fin 262) = [256, 130, 66, 34, 18, 10, 6, 1] by decide]
  exact space1626_lower

theorem plane486_source0245 : plane486GenConfig.sourceLb (245 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (245 : Fin 262)) := by
  change plane486GenSourceLb (245 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (245 : Fin 262)))
  rw [show plane486GenSourceLb (245 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (245 : Fin 262) = [257, 128, 64, 32, 17, 8, 4, 2] by decide]
  exact space1658_lower

theorem plane486_source0246 : plane486GenConfig.sourceLb (246 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (246 : Fin 262)) := by
  change plane486GenSourceLb (246 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (246 : Fin 262)))
  rw [show plane486GenSourceLb (246 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (246 : Fin 262) = [256, 128, 65, 32, 17, 8, 5, 2] by decide]
  exact space1632_lower

theorem plane486_source0247 : plane486GenConfig.sourceLb (247 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (247 : Fin 262)) := by
  change plane486GenSourceLb (247 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (247 : Fin 262)))
  rw [show plane486GenSourceLb (247 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (247 : Fin 262) = [256, 128, 65, 33, 16, 9, 5, 3] by decide]
  exact space1638_lower

theorem plane486_source0248 : plane486GenConfig.sourceLb (248 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (248 : Fin 262)) := by
  change plane486GenSourceLb (248 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (248 : Fin 262)))
  rw [show plane486GenSourceLb (248 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (248 : Fin 262) = [256, 129, 65, 32, 16, 9, 5, 3] by decide]
  exact space1636_lower

theorem plane486_source0249 : plane486GenConfig.sourceLb (249 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (249 : Fin 262)) := by
  change plane486GenSourceLb (249 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (249 : Fin 262)))
  rw [show plane486GenSourceLb (249 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (249 : Fin 262) = [257, 129, 64, 33, 17, 9, 4, 3] by decide]
  exact space2250_lower

theorem plane486_source0250 : plane486GenConfig.sourceLb (250 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (250 : Fin 262)) := by
  change plane486GenSourceLb (250 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (250 : Fin 262)))
  rw [show plane486GenSourceLb (250 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (250 : Fin 262) = [257, 128, 64, 33, 16, 9, 4, 3] by decide]
  exact space1646_lower

theorem plane486_source0251 : plane486GenConfig.sourceLb (251 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (251 : Fin 262)) := by
  change plane486GenSourceLb (251 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (251 : Fin 262)))
  rw [show plane486GenSourceLb (251 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (251 : Fin 262) = [257, 129, 64, 32, 16, 9, 4, 3] by decide]
  exact space1648_lower

theorem plane486_source0252 : plane486GenConfig.sourceLb (252 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (252 : Fin 262)) := by
  change plane486GenSourceLb (252 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (252 : Fin 262)))
  rw [show plane486GenSourceLb (252 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (252 : Fin 262) = [256, 128, 65, 33, 17, 8, 5, 2] by decide]
  exact space1650_lower

theorem plane486_source0253 : plane486GenConfig.sourceLb (253 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (253 : Fin 262)) := by
  change plane486GenSourceLb (253 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (253 : Fin 262)))
  rw [show plane486GenSourceLb (253 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (253 : Fin 262) = [256, 129, 65, 32, 17, 8, 5, 2] by decide]
  exact space1653_lower

theorem plane486_source0254 : plane486GenConfig.sourceLb (254 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (254 : Fin 262)) := by
  change plane486GenSourceLb (254 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (254 : Fin 262)))
  rw [show plane486GenSourceLb (254 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (254 : Fin 262) = [256, 129, 65, 33, 16, 8, 5, 2] by decide]
  exact space2251_lower

theorem plane486_source0255 : plane486GenConfig.sourceLb (255 : Fin 262) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (255 : Fin 262)) := by
  change plane486GenSourceLb (255 : Fin 262) ≤
    frozenWangTable.L0 (spanCodes (plane486GenSourceBasis (255 : Fin 262)))
  rw [show plane486GenSourceLb (255 : Fin 262) = 9 by decide,
      show plane486GenSourceBasis (255 : Fin 262) = [256, 129, 64, 33, 17, 8, 4, 2] by decide]
  exact space1630_lower

theorem plane486_sourceBlock007 (offset : Fin 32)
    (hlt : 7 * 32 + offset.val < 262) :
    plane486GenConfig.sourceLb (Fin.mk (7 * 32 + offset.val) hlt) ≤ frozenWangTable.L0 (plane486GenConfig.sourceU (Fin.mk (7 * 32 + offset.val) hlt)) := by
  revert hlt
  match offset with
  | ⟨0, _⟩ => intro hlt; exact plane486_source0224
  | ⟨1, _⟩ => intro hlt; exact plane486_source0225
  | ⟨2, _⟩ => intro hlt; exact plane486_source0226
  | ⟨3, _⟩ => intro hlt; exact plane486_source0227
  | ⟨4, _⟩ => intro hlt; exact plane486_source0228
  | ⟨5, _⟩ => intro hlt; exact plane486_source0229
  | ⟨6, _⟩ => intro hlt; exact plane486_source0230
  | ⟨7, _⟩ => intro hlt; exact plane486_source0231
  | ⟨8, _⟩ => intro hlt; exact plane486_source0232
  | ⟨9, _⟩ => intro hlt; exact plane486_source0233
  | ⟨10, _⟩ => intro hlt; exact plane486_source0234
  | ⟨11, _⟩ => intro hlt; exact plane486_source0235
  | ⟨12, _⟩ => intro hlt; exact plane486_source0236
  | ⟨13, _⟩ => intro hlt; exact plane486_source0237
  | ⟨14, _⟩ => intro hlt; exact plane486_source0238
  | ⟨15, _⟩ => intro hlt; exact plane486_source0239
  | ⟨16, _⟩ => intro hlt; exact plane486_source0240
  | ⟨17, _⟩ => intro hlt; exact plane486_source0241
  | ⟨18, _⟩ => intro hlt; exact plane486_source0242
  | ⟨19, _⟩ => intro hlt; exact plane486_source0243
  | ⟨20, _⟩ => intro hlt; exact plane486_source0244
  | ⟨21, _⟩ => intro hlt; exact plane486_source0245
  | ⟨22, _⟩ => intro hlt; exact plane486_source0246
  | ⟨23, _⟩ => intro hlt; exact plane486_source0247
  | ⟨24, _⟩ => intro hlt; exact plane486_source0248
  | ⟨25, _⟩ => intro hlt; exact plane486_source0249
  | ⟨26, _⟩ => intro hlt; exact plane486_source0250
  | ⟨27, _⟩ => intro hlt; exact plane486_source0251
  | ⟨28, _⟩ => intro hlt; exact plane486_source0252
  | ⟨29, _⟩ => intro hlt; exact plane486_source0253
  | ⟨30, _⟩ => intro hlt; exact plane486_source0254
  | ⟨31, _⟩ => intro hlt; exact plane486_source0255
  | ⟨k + 32, h⟩ => intro hlt; simp only [Fin.val_mk] at hlt; omega

end QiushiMatmul.FrozenWang
