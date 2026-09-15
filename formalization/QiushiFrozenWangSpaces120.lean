import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3840_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 35, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 131), (131, 259), (64, 256), (35, 138), (16, 511), (10, 227), (7, 130)]
    (codeMat 285) (codeMat 214) (codeMat 214) false
    det285 det214 inv214
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3840_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 35, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3840_orbit
  simpa only [lower14] using h

theorem space3841_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 66, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 257), (130, 2), (66, 327), (32, 8), (16, 16), (10, 184), (7, 256)]
    (codeMat 85) (codeMat 93) (codeMat 372) false
    det85 det93 inv93
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3841_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space3841_orbit
  simpa only [lower10] using h

theorem space3842_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 387), (129, 385), (65, 384), (35, 105), (18, 511), (10, 503), (6, 130)]
    (codeMat 340) (codeMat 478) (codeMat 445) false
    det340 det478 inv478
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3842_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3842_orbit
  simpa only [lower14] using h

theorem space3843_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 65, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 508), (130, 1), (65, 3), (32, 256), (18, 8), (10, 136), (6, 360)]
    (codeMat 157) (codeMat 267) (codeMat 282) false
    det157 det267 inv267
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3843_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3843_orbit
  simpa only [lower14] using h

theorem space3844_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 128, 67, 34, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 326), (128, 2), (67, 327), (34, 176), (16, 16), (10, 184), (6, 256)]
    (codeMat 84) (codeMat 377) (codeMat 369) false
    det84 det377 inv377
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3844_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 34, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space3844_orbit
  simpa only [lower10] using h

theorem space3845_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 264), (131, 488), (64, 360), (35, 276), (18, 511), (10, 381), (5, 8)]
    (codeMat 335) (codeMat 467) (codeMat 339) false
    det335 det467 inv467
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3845_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3845_orbit
  simpa only [lower14] using h

theorem space3846_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 67, 34, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 381), (129, 373), (67, 235), (34, 385), (18, 384), (10, 387), (5, 130)]
    (codeMat 226) (codeMat 501) (codeMat 494) false
    det226 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3846_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 34, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3846_orbit
  simpa only [lower14] using h

theorem space3847_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 352), (129, 480), (64, 256), (33, 361), (18, 3), (10, 508), (5, 360)]
    (codeMat 299) (codeMat 86) (codeMat 212) false
    det299 det86 inv86
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3847_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3847_orbit
  simpa only [lower14] using h

theorem space3848_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 30), (128, 3), (66, 31), (33, 392), (17, 224), (10, 480), (5, 8)]
    (codeMat 204) (codeMat 379) (codeMat 247) false
    det204 det379 inv379
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3848_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3848_orbit
  simpa only [lower14] using h

theorem space3849_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 264), (131, 480), (65, 256), (35, 149), (18, 3), (10, 508), (4, 360)]
    (codeMat 355) (codeMat 342) (codeMat 215) false
    det355 det342 inv342
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3849_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3849_orbit
  simpa only [lower14] using h

theorem space3850_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (129, 488), (65, 360), (33, 105), (18, 511), (10, 381), (4, 8)]
    (codeMat 270) (codeMat 215) (codeMat 342) false
    det270 det215 inv215
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3850_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3850_orbit
  simpa only [lower14] using h

theorem space3851_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 35, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 96), (131, 480), (67, 224), (35, 105), (16, 511), (10, 227), (4, 8)]
    (codeMat 271) (codeMat 159) (codeMat 230) false
    det271 det159 inv159
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3851_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 35, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3851_orbit
  simpa only [lower14] using h

theorem space3852_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 128, 68, 37, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 483), (128, 360), (68, 252), (37, 227), (21, 235), (9, 511), (3, 130)]
    (codeMat 407) (codeMat 459) (codeMat 346) false
    det407 det459 inv459
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3852_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 68, 37, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3852_orbit
  simpa only [lower14] using h

theorem space3853_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 65, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 384), (132, 232), (65, 128), (37, 406), (20, 235), (9, 130), (3, 8)]
    (codeMat 334) (codeMat 314) (codeMat 271) false
    det334 det314 inv314
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3853_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3853_orbit
  simpa only [lower14] using h

theorem space3854_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 69, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (129, 363), (69, 150), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 213) (codeMat 122) (codeMat 460) false
    det213 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3854_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 69, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3854_orbit
  simpa only [lower14] using h

theorem space3855_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 68, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 8), (128, 384), (68, 136), (36, 1), (20, 510), (9, 3), (3, 360)]
    (codeMat 299) (codeMat 157) (codeMat 486) false
    det299 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3855_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3855_orbit
  simpa only [lower14] using h

theorem space3856_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 64, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 384), (129, 104), (64, 8), (33, 510), (20, 148), (9, 1), (3, 360)]
    (codeMat 355) (codeMat 417) (codeMat 177) false
    det355 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3856_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 64, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3856_orbit
  simpa only [lower14] using h

theorem space3857_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 68, 32, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 1), (132, 257), (68, 385), (32, 8), (20, 105), (9, 511), (3, 130)]
    (codeMat 277) (codeMat 207) (codeMat 370) false
    det277 det207 inv207
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3857_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 32, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3857_orbit
  simpa only [lower14] using h

theorem space3858_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (129, 91), (64, 9), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 307) (codeMat 311) false
    det95 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3858_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3858_orbit
  simpa only [lower11] using h

theorem space3859_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 64, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (132, 148), (64, 1), (32, 128), (16, 256), (9, 8), (3, 360)]
    (codeMat 156) (codeMat 161) (codeMat 161) false
    det156 det161 inv161
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3859_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3859_orbit
  simpa only [lower14] using h

theorem space3860_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 144, 80, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 327), (144, 325), (80, 326), (49, 176), (9, 432), (5, 8), (3, 24)]
    (codeMat 140) (codeMat 494) (codeMat 501) false
    det140 det494 inv494
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3860_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 80, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3860_orbit
  simpa only [lower10] using h

theorem space3861_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 129, 64, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 381), (129, 104), (64, 8), (48, 130), (9, 1), (5, 384), (3, 256)]
    (codeMat 99) (codeMat 423) (codeMat 181) false
    det99 det423 inv423
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3861_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 129, 64, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3861_orbit
  simpa only [lower14] using h

theorem space3862_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 144, 65, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 508), (144, 3), (65, 9), (33, 352), (9, 8), (4, 256), (3, 128)]
    (codeMat 94) (codeMat 275) (codeMat 275) false
    det94 det275 inv275
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3862_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 65, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3862_orbit
  simpa only [lower14] using h

theorem space3863_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 193, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (193, 199), (33, 23), (16, 32), (9, 63), (4, 2), (3, 3)]
    (codeMat 273) (codeMat 233) (codeMat 233) false
    det273 det233 inv233
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3863_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 193, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3863_orbit
  simpa only [lower11] using h

theorem space3864_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 68, 36, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 1), (128, 128), (68, 385), (36, 8), (21, 276), (8, 511), (2, 130)]
    (codeMat 285) (codeMat 93) (codeMat 372) false
    det285 det93 inv93
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3864_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 36, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3864_orbit
  simpa only [lower14] using h

theorem space3865_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 68, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 8), (132, 264), (68, 136), (32, 1), (21, 149), (8, 3), (2, 360)]
    (codeMat 298) (codeMat 143) (codeMat 482) false
    det298 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3865_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3865_orbit
  simpa only [lower14] using h

theorem space3866_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 129, 68, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 414), (129, 227), (68, 373), (36, 360), (20, 362), (8, 3), (2, 511)]
    (codeMat 482) (codeMat 415) (codeMat 253) false
    det482 det415 inv415
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3866_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 68, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3866_orbit
  simpa only [lower14] using h

theorem space3867_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 65, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 488), (133, 96), (65, 128), (33, 23), (16, 1), (8, 2), (2, 8)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    det330 det302 inv302
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3867_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3867_orbit
  simpa only [lower14] using h

theorem space3868_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 68, 32, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 9), (132, 137), (68, 393), (32, 8), (22, 138), (10, 227), (1, 511)]
    (codeMat 279) (codeMat 95) (codeMat 244) false
    det279 det95 inv95
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3868_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 32, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3868_orbit
  simpa only [lower14] using h

theorem space3869_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 64, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (132, 21), (64, 1), (32, 128), (18, 360), (10, 104), (1, 8)]
    (codeMat 140) (codeMat 163) (codeMat 165) false
    det140 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3869_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3869_orbit
  simpa only [lower14] using h

theorem space3870_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [274, 130, 66, 50, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(274, 441), (130, 511), (66, 186), (50, 440), (10, 184), (4, 8), (1, 16)]
    (codeMat 142) (codeMat 158) (codeMat 358) false
    det142 det158 inv158
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3870_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 130, 66, 50, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3870_orbit
  simpa only [lower10] using h

theorem space3871_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(260, 325), (128, 2), (68, 324), (32, 40), (20, 336), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    det84 det340 inv340
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3871_lower : 9 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3871_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
