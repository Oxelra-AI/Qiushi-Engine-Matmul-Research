import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3072_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 65, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (130, 32), (65, 40), (33, 198), (17, 68), (10, 69), (6, 128)]
    (codeMat 107) (codeMat 481) (codeMat 185) false
    det107 det481 inv481
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3072_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space3072_orbit
  simpa only [lower11] using h

theorem space3073_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 128, 66, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (128, 219), (66, 82), (34, 240), (18, 216), (10, 208), (1, 128)]
    (codeMat 87) (codeMat 314) (codeMat 271) false
    det87 det314 inv314
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3073_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 66, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3073_orbit
  simpa only [lower11] using h

theorem space3074_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 130, 64, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 227), (130, 256), (64, 130), (32, 511), (10, 150), (6, 3), (1, 2)]
    (codeMat 369) (codeMat 428) (codeMat 107) false
    det369 det428 inv428
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3074_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 130, 64, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3074_orbit
  simpa only [lower14] using h

theorem space3075_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 144, 66, 34, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 219), (144, 54), (66, 121), (34, 240), (10, 112), (6, 40), (1, 8)]
    (codeMat 143) (codeMat 181) (codeMat 423) false
    det143 det181 inv181
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3075_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 66, 34, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3075_orbit
  simpa only [lower11] using h

theorem space3076_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 146, 66, 34, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 243), (146, 54), (66, 113), (34, 240), (10, 112), (6, 40), (1, 8)]
    (codeMat 142) (codeMat 181) (codeMat 423) false
    det142 det181 inv181
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3076_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 146, 66, 34, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3076_orbit
  simpa only [lower11] using h

theorem space3077_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [386, 64, 32, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(386, 69), (64, 128), (32, 32), (16, 40), (10, 21), (6, 1), (1, 2)]
    (codeMat 273) (codeMat 394) (codeMat 330) false
    det273 det394 inv394
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3077_lower : 12 ≤ frozenWangTable.L0 (spanCodes [386, 64, 32, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3077_orbit
  simpa only [lower11] using h

theorem space3078_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [263, 135, 68, 36, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(263, 402), (135, 411), (68, 283), (36, 32), (18, 40), (10, 170)]
    (codeMat 351) (codeMat 459) (codeMat 346) false
    det351 det459 inv459
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3078_lower : 12 ≤ frozenWangTable.L0 (spanCodes [263, 135, 68, 36, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 43 space3078_orbit
  simpa only [lower43] using h

theorem space3079_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 65, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 182), (129, 228), (65, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 94) (codeMat 489) (codeMat 241) false
    det94 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3079_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space3079_orbit
  simpa only [lower11] using h

theorem space3080_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 483), (128, 9), (66, 119), (34, 136), (18, 8), (10, 392), (7, 360)]
    (codeMat 159) (codeMat 111) (codeMat 412) false
    det159 det111 inv111
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3080_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3080_orbit
  simpa only [lower14] using h

theorem space3081_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 66, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (129, 70), (66, 71), (34, 424), (18, 432), (10, 440), (7, 256)]
    (codeMat 85) (codeMat 477) (codeMat 431) false
    det85 det477 inv477
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3081_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space3081_orbit
  simpa only [lower10] using h

theorem space3082_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 67, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 284), (129, 414), (67, 235), (35, 264), (18, 384), (10, 232), (7, 8)]
    (codeMat 207) (codeMat 409) (codeMat 473) false
    det207 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3082_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3082_orbit
  simpa only [lower14] using h

theorem space3083_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 64, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 259), (130, 2), (64, 325), (32, 24), (16, 16), (10, 168), (7, 256)]
    (codeMat 85) (codeMat 117) (codeMat 380) false
    det85 det117 inv117
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3083_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space3083_orbit
  simpa only [lower10] using h

theorem space3084_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 32, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 29), (129, 31), (64, 3), (32, 360), (17, 480), (10, 224), (7, 8)]
    (codeMat 204) (codeMat 415) (codeMat 253) false
    det204 det415 inv415
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3084_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3084_orbit
  simpa only [lower14] using h

theorem space3085_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 67, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 2), (131, 196), (67, 199), (35, 80), (18, 32), (10, 248), (4, 128)]
    (codeMat 92) (codeMat 233) (codeMat 233) false
    det92 det233 inv233
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3085_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space3085_orbit
  simpa only [lower11] using h

theorem space3086_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 2), (128, 1), (66, 70), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    det84 det106 inv106
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3086_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space3086_orbit
  simpa only [lower11] using h

theorem space3087_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 64, 32, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 257), (130, 2), (64, 325), (32, 8), (16, 16), (10, 168), (5, 256)]
    (codeMat 85) (codeMat 85) (codeMat 340) false
    det85 det85 inv85
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3087_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 32, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space3087_orbit
  simpa only [lower10] using h

theorem space3088_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 66, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 284), (131, 414), (66, 373), (34, 20), (17, 30), (10, 29), (5, 8)]
    (codeMat 459) (codeMat 465) (codeMat 465) false
    det459 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3088_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 66, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3088_orbit
  simpa only [lower14] using h

theorem space3089_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 66, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 160), (129, 120), (66, 112), (34, 196), (17, 71), (10, 70), (5, 128)]
    (codeMat 107) (codeMat 474) (codeMat 395) false
    det107 det474 inv474
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3089_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3089_orbit
  simpa only [lower11] using h

theorem space3090_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 32, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 509), (131, 361), (64, 360), (32, 130), (17, 105), (10, 97), (5, 511)]
    (codeMat 477) (codeMat 225) (codeMat 169) false
    det477 det225 inv225
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3090_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3090_orbit
  simpa only [lower14] using h

theorem space3091_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 148), (129, 149), (64, 2), (32, 256), (20, 96), (8, 128), (2, 360)]
    (codeMat 156) (codeMat 394) (codeMat 330) false
    det156 det394 inv394
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3091_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3091_orbit
  simpa only [lower14] using h

theorem space3092_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 144, 81, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 161), (144, 3), (81, 484), (49, 160), (8, 256), (4, 8), (2, 24)]
    (codeMat 142) (codeMat 86) (codeMat 212) false
    det142 det86 inv86
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3092_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 144, 81, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space3092_orbit
  simpa only [lower10] using h

theorem space3093_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 145, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 247), (145, 246), (81, 245), (49, 264), (8, 360), (5, 128), (2, 384)]
    (codeMat 92) (codeMat 501) (codeMat 494) false
    det92 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3093_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3093_orbit
  simpa only [lower14] using h

theorem space3094_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 133, 64, 32, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 326), (133, 327), (64, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    det92 det443 inv443
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3094_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 32, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3094_orbit
  simpa only [lower10] using h

theorem space3095_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 64, 32, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 70), (129, 69), (64, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 419) (codeMat 183) false
    det92 det419 inv419
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3095_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3095_orbit
  simpa only [lower10] using h

theorem space3096_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 145, 65, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 89), (145, 30), (65, 219), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 142) (codeMat 157) (codeMat 486) false
    det142 det157 inv157
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3096_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 145, 65, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3096_orbit
  simpa only [lower11] using h

theorem space3097_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [384, 65, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(384, 128), (65, 216), (33, 60), (16, 54), (9, 3), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 409) (codeMat 473) false
    det267 det409 inv409
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3097_lower : 12 ≤ frozenWangTable.L0 (spanCodes [384, 65, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3097_orbit
  simpa only [lower11] using h

theorem space3098_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 66, 34, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 70), (130, 2), (66, 327), (34, 176), (16, 16), (10, 184), (6, 256)]
    (codeMat 85) (codeMat 377) (codeMat 369) false
    det85 det377 inv377
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3098_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 34, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space3098_orbit
  simpa only [lower10] using h

theorem space3099_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 64, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 228), (130, 219), (64, 54), (32, 32), (18, 216), (10, 240), (5, 128)]
    (codeMat 86) (codeMat 346) (codeMat 459) false
    det86 det346 inv346
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3099_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3099_orbit
  simpa only [lower11] using h

theorem space3100_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 392), (129, 224), (66, 480), (34, 30), (16, 3), (10, 31), (5, 8)]
    (codeMat 330) (codeMat 379) (codeMat 247) false
    det330 det379 inv379
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3100_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3100_orbit
  simpa only [lower14] using h

theorem space3101_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 32, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 362), (131, 508), (64, 511), (32, 128), (16, 256), (10, 224), (5, 360)]
    (codeMat 157) (codeMat 233) (codeMat 233) false
    det157 det233 inv233
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3101_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3101_orbit
  simpa only [lower14] using h

theorem space3102_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 144, 64, 32, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 138), (144, 54), (64, 219), (32, 128), (9, 216), (5, 8), (3, 40)]
    (codeMat 143) (codeMat 185) (codeMat 481) false
    det143 det185 inv185
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3102_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 64, 32, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3102_orbit
  simpa only [lower11] using h

theorem space3103_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [262, 134, 70, 38, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(262, 71), (134, 70), (70, 68), (38, 440), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 500) (codeMat 94) false
    det92 det500 inv500
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3103_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 70, 38, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3103_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
