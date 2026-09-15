import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3296_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 192, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 224), (192, 128), (35, 11), (17, 20), (10, 22), (7, 8)]
    (codeMat 267) (codeMat 236) (codeMat 123) false
    det267 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3296_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 192, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3296_orbit
  simpa only [lower35] using h

theorem space3297_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 65, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 429), (144, 390), (65, 128), (39, 295), (10, 294)]
    (codeMat 379) (codeMat 188) (codeMat 103) false
    det379 det188 inv188
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3297_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 65, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3297_orbit
  simpa only [lower187] using h

theorem space3298_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 147, 65, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 429), (147, 10), (65, 128), (36, 390), (10, 139)]
    (codeMat 382) (codeMat 314) (codeMat 271) false
    det382 det314 inv314
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3298_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 147, 65, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3298_orbit
  simpa only [lower187] using h

theorem space3299_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 68, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (132, 96), (68, 224), (39, 148), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 459) (codeMat 346) false
    det299 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3299_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 68, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3299_orbit
  simpa only [lower35] using h

theorem space3300_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 131, 67, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 252), (131, 31), (67, 28), (39, 148), (17, 22), (10, 20)]
    (codeMat 95) (codeMat 314) (codeMat 271) true
    det95 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3300_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3300_orbit
  simpa only [lower35] using h

theorem space3301_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 147, 83, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 453), (147, 447), (83, 446), (49, 272), (10, 112), (7, 256)]
    (codeMat 92) (codeMat 478) (codeMat 445) false
    det92 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space3301_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 147, 83, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space3301_orbit
  simpa only [lower69] using h

theorem space3302_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 195, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 232), (195, 128), (35, 11), (17, 22), (10, 20), (7, 8)]
    (codeMat 331) (codeMat 244) (codeMat 95) false
    det331 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3302_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 195, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3302_orbit
  simpa only [lower35] using h

theorem space3303_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 195, 48, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 170), (195, 32), (48, 128), (10, 263), (5, 390)]
    (codeMat 171) (codeMat 415) (codeMat 253) false
    det171 det415 inv415
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3303_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 195, 48, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 187 space3303_orbit
  simpa only [lower187] using h

theorem space3304_orbit :
    frozenWangTable.OrbitImage 112 (spanCodes [258, 194, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 112 [(258, 274), (194, 272), (36, 9), (17, 96), (10, 104)]
    (codeMat 99) (codeMat 236) (codeMat 123) true
    det99 det236 inv236
    (by rw [basis112]; decide +kernel)
    (by rw [basis112]; decide +kernel)

theorem space3304_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 112 space3304_orbit
  simpa only [lower112] using h

theorem space3305_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 144, 83, 49, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 368), (144, 27), (83, 283), (49, 446), (10, 479), (5, 16)]
    (codeMat 335) (codeMat 351) (codeMat 239) false
    det335 det351 inv351
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space3305_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 83, 49, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space3305_orbit
  simpa only [lower69] using h

theorem space3306_orbit :
    frozenWangTable.OrbitImage 119 (spanCodes [256, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 119 [(256, 256), (36, 32), (20, 33), (8, 2), (2, 45)]
    (codeMat 282) (codeMat 394) (codeMat 330) false
    det282 det394 inv394
    (by rw [basis119]; decide +kernel)
    (by rw [basis119]; decide +kernel)

theorem space3306_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 119 space3306_orbit
  simpa only [lower119] using h

theorem space3307_orbit :
    frozenWangTable.OrbitImage 119 (spanCodes [256, 129, 65, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 119 [(256, 2), (129, 33), (65, 32), (8, 256), (2, 45)]
    (codeMat 172) (codeMat 226) (codeMat 141) false
    det172 det226 inv226
    (by rw [basis119]; decide +kernel)
    (by rw [basis119]; decide +kernel)

theorem space3307_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 119 space3307_orbit
  simpa only [lower119] using h

theorem space3308_orbit :
    frozenWangTable.OrbitImage 143 (spanCodes [256, 177, 65, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 143 [(256, 432), (177, 116), (65, 2), (8, 1), (2, 32)]
    (codeMat 106) (codeMat 305) (codeMat 305) true
    det106 det305 inv305
    (by rw [basis143]; decide +kernel)
    (by rw [basis143]; decide +kernel)

theorem space3308_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 177, 65, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 143 space3308_orbit
  simpa only [lower143] using h

theorem space3309_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [256, 193, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(256, 192), (193, 324), (37, 31), (20, 11), (8, 32), (2, 1)]
    (codeMat 273) (codeMat 102) (codeMat 156) false
    det273 det102 inv102
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3309_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 193, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 74 space3309_orbit
  simpa only [lower74] using h

theorem space3310_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 133, 68, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 1), (133, 322), (68, 68), (37, 328), (20, 80), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3310_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 133, 68, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3310_orbit
  simpa only [lower17] using h

theorem space3311_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 69, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 63), (129, 274), (69, 228), (33, 312), (21, 208), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 372) (codeMat 93) false
    det86 det372 inv372
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3311_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 69, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3311_orbit
  simpa only [lower17] using h

theorem space3312_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 68, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 390), (129, 450), (68, 197), (33, 240), (21, 80), (8, 360), (2, 128)]
    (codeMat 93) (codeMat 369) (codeMat 377) false
    det93 det369 inv369
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3312_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 68, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3312_orbit
  simpa only [lower17] using h

theorem space3313_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 69, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (129, 402), (69, 228), (33, 280), (20, 208), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 116) (codeMat 92) false
    det87 det116 inv116
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3313_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 69, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3313_orbit
  simpa only [lower17] using h

theorem space3314_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 68, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 1), (129, 322), (68, 69), (37, 328), (20, 208), (8, 360), (2, 128)]
    (codeMat 92) (codeMat 85) (codeMat 340) false
    det92 det85 inv85
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3314_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 68, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3314_orbit
  simpa only [lower17] using h

theorem space3315_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 133, 68, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (133, 274), (68, 429), (33, 408), (20, 80), (8, 360), (2, 128)]
    (codeMat 94) (codeMat 117) (codeMat 380) false
    det94 det117 inv117
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3315_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 133, 68, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3315_orbit
  simpa only [lower17] using h

theorem space3316_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 144, 80, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 408), (144, 32), (80, 406), (50, 168), (10, 170), (5, 45)]
    (codeMat 407) (codeMat 369) (codeMat 377) true
    det407 det369 inv369
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3316_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 144, 80, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space3316_orbit
  simpa only [lower55] using h

theorem space3317_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 192, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 408), (192, 45), (33, 406), (19, 166), (10, 306), (5, 438)]
    (codeMat 215) (codeMat 241) (codeMat 489) true
    det215 det241 inv241
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3317_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 192, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space3317_orbit
  simpa only [lower55] using h

theorem space3318_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (68, 80), (32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    det266 det161 inv161
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3318_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3318_orbit
  simpa only [lower11] using h

theorem space3319_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (129, 68), (33, 20), (16, 8), (8, 32), (4, 2), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    det273 det98 inv98
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3319_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3319_orbit
  simpa only [lower11] using h

theorem space3320_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [257, 177, 113, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(257, 43), (177, 171), (113, 162), (9, 432), (5, 3), (3, 1)]
    (codeMat 425) (codeMat 478) (codeMat 445) false
    det425 det478 inv478
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3320_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 177, 113, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 43 space3320_orbit
  simpa only [lower43] using h

theorem space3321_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [257, 165, 101, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(257, 343), (165, 95), (101, 90), (17, 15), (9, 9), (3, 7)]
    (codeMat 491) (codeMat 313) (codeMat 313) true
    det491 det313 inv313
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3321_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 165, 101, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 25 space3321_orbit
  simpa only [lower25] using h

theorem space3322_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 32), (128, 8), (68, 20), (20, 68), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    det161 det266 inv266
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3322_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3322_orbit
  simpa only [lower11] using h

theorem space3323_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 81, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (145, 246), (81, 245), (33, 264), (8, 360), (5, 256), (2, 384)]
    (codeMat 92) (codeMat 213) (codeMat 470) false
    det92 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3323_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 81, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3323_orbit
  simpa only [lower14] using h

theorem space3324_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [257, 144, 65, 53, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(257, 441), (144, 3), (65, 9), (53, 162), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 311) (codeMat 307) false
    det478 det311 inv311
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3324_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 65, 53, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 43 space3324_orbit
  simpa only [lower43] using h

theorem space3325_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 3), (129, 20), (64, 2), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    det140 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3325_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3325_orbit
  simpa only [lower11] using h

theorem space3326_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 144, 81, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (144, 130), (81, 509), (33, 264), (8, 360), (5, 256), (2, 128)]
    (codeMat 95) (codeMat 85) (codeMat 340) false
    det95 det85 inv85
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3326_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 81, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3326_orbit
  simpa only [lower14] using h

theorem space3327_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 144, 65, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (144, 130), (65, 9), (49, 104), (8, 8), (5, 384), (2, 128)]
    (codeMat 87) (codeMat 309) (codeMat 309) false
    det87 det309 inv309
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3327_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 65, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3327_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
