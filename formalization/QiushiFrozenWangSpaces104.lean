import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3328_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 65, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (145, 502), (65, 8), (48, 3), (8, 1), (5, 256), (2, 384)]
    (codeMat 106) (codeMat 405) (codeMat 407) false
    det106 det405 inv405
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3328_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 65, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3328_orbit
  simpa only [lower14] using h

theorem space3329_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 81, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (129, 480), (81, 28), (48, 1), (8, 3), (5, 384), (2, 256)]
    (codeMat 106) (codeMat 397) (codeMat 250) false
    det106 det397 inv397
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3329_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 81, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3329_orbit
  simpa only [lower14] using h

theorem space3330_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 81, 33, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (145, 29), (81, 413), (33, 149), (8, 360), (4, 2), (2, 3)]
    (codeMat 305) (codeMat 115) (codeMat 492) false
    det305 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3330_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 81, 33, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3330_orbit
  simpa only [lower14] using h

theorem space3331_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [258, 135, 71, 34, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(258, 411), (135, 274), (71, 283), (34, 435), (18, 432), (10, 433)]
    (codeMat 370) (codeMat 477) (codeMat 431) false
    det370 det477 inv477
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3331_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 135, 71, 34, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 43 space3331_orbit
  simpa only [lower43] using h

theorem space3332_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [258, 135, 66, 34, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(258, 350), (135, 269), (66, 343), (34, 344), (23, 264), (10, 336)]
    (codeMat 214) (codeMat 491) (codeMat 375) false
    det214 det491 inv491
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3332_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 34, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 25 space3332_orbit
  simpa only [lower25] using h

theorem space3333_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 36, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 488), (130, 360), (66, 104), (36, 511), (20, 381), (10, 105), (1, 8)]
    (codeMat 270) (codeMat 423) (codeMat 181) false
    det270 det423 inv423
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3333_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 36, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3333_orbit
  simpa only [lower14] using h

theorem space3334_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 32), (129, 80), (64, 8), (33, 68), (16, 2), (8, 1), (2, 128)]
    (codeMat 98) (codeMat 273) (codeMat 273) false
    det98 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3334_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3334_orbit
  simpa only [lower11] using h

theorem space3335_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 68, 37, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (129, 406), (68, 227), (37, 259), (16, 128), (8, 256), (2, 130)]
    (codeMat 171) (codeMat 372) (codeMat 93) false
    det171 det372 inv372
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3335_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 68, 37, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3335_orbit
  simpa only [lower14] using h

theorem space3336_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 69, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (133, 509), (69, 508), (33, 480), (17, 96), (8, 256), (2, 360)]
    (codeMat 156) (codeMat 230) (codeMat 159) false
    det156 det230 inv230
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3336_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 69, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3336_orbit
  simpa only [lower14] using h

theorem space3337_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 64, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (133, 118), (64, 128), (33, 406), (20, 227), (8, 130), (2, 511)]
    (codeMat 286) (codeMat 410) (codeMat 331) false
    det286 det410 inv410
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3337_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3337_orbit
  simpa only [lower14] using h

theorem space3338_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 69, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (133, 509), (69, 510), (36, 8), (20, 264), (8, 384), (2, 360)]
    (codeMat 156) (codeMat 206) (codeMat 498) false
    det156 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3338_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 69, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3338_orbit
  simpa only [lower14] using h

theorem space3339_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 65, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (133, 404), (65, 9), (33, 105), (21, 276), (8, 8), (2, 130)]
    (codeMat 407) (codeMat 277) (codeMat 277) false
    det407 det277 inv277
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3339_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3339_orbit
  simpa only [lower14] using h

theorem space3340_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (129, 264), (65, 8), (37, 510), (21, 509), (8, 1), (2, 360)]
    (codeMat 298) (codeMat 419) (codeMat 183) false
    det298 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3340_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3340_orbit
  simpa only [lower14] using h

theorem space3341_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 133, 69, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (133, 210), (69, 237), (37, 240), (21, 208), (8, 40), (2, 128)]
    (codeMat 86) (codeMat 369) (codeMat 377) false
    det86 det369 inv369
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3341_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 69, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3341_orbit
  simpa only [lower11] using h

theorem space3342_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 257), (129, 129), (65, 1), (37, 105), (20, 414), (9, 8), (3, 130)]
    (codeMat 285) (codeMat 279) (codeMat 279) false
    det285 det279 inv279
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3342_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3342_orbit
  simpa only [lower14] using h

theorem space3343_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [257, 197, 36, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(257, 336), (197, 88), (36, 5), (17, 14), (9, 7), (3, 8)]
    (codeMat 331) (codeMat 477) (codeMat 431) false
    det331 det477 inv477
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3343_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 197, 36, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 25 space3343_orbit
  simpa only [lower25] using h

theorem space3344_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 65, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 130), (133, 413), (65, 9), (36, 128), (17, 96), (8, 8), (2, 360)]
    (codeMat 215) (codeMat 163) (codeMat 165) false
    det215 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3344_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3344_orbit
  simpa only [lower14] using h

theorem space3345_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 132, 69, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 219), (132, 82), (69, 228), (36, 216), (20, 208), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 116) (codeMat 92) false
    det87 det116 inv116
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3345_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 69, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3345_orbit
  simpa only [lower11] using h

theorem space3346_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 67, 34, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 138), (129, 414), (67, 235), (34, 131), (18, 3), (10, 387), (6, 130)]
    (codeMat 171) (codeMat 87) (codeMat 468) false
    det171 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3346_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 67, 34, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3346_orbit
  simpa only [lower14] using h

theorem space3347_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 131, 64, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 71), (131, 326), (64, 325), (34, 440), (18, 432), (10, 424), (7, 256)]
    (codeMat 85) (codeMat 501) (codeMat 494) false
    det85 det501 inv501
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3347_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space3347_orbit
  simpa only [lower10] using h

theorem space3348_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 373), (131, 276), (67, 406), (33, 508), (17, 148), (10, 150), (5, 511)]
    (codeMat 491) (codeMat 244) (codeMat 95) false
    det491 det244 inv244
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3348_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3348_orbit
  simpa only [lower14] using h

theorem space3349_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 64, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 240), (130, 216), (64, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 98) (codeMat 370) (codeMat 207) false
    det98 det370 inv370
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3349_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3349_orbit
  simpa only [lower11] using h

theorem space3350_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 66, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 68), (129, 197), (66, 198), (33, 160), (18, 40), (10, 240), (5, 128)]
    (codeMat 93) (codeMat 458) (codeMat 458) false
    det93 det458 inv458
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3350_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3350_orbit
  simpa only [lower11] using h

theorem space3351_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 66, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 55), (130, 63), (66, 31), (50, 71), (10, 199), (6, 1), (1, 3)]
    (codeMat 161) (codeMat 443) (codeMat 254) false
    det161 det443 inv443
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3351_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3351_orbit
  simpa only [lower11] using h

theorem space3352_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 67, 34, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 257), (128, 325), (67, 327), (34, 264), (17, 168), (10, 184), (6, 256)]
    (codeMat 93) (codeMat 207) (codeMat 370) false
    det93 det207 inv207
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3352_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 34, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space3352_orbit
  simpa only [lower10] using h

theorem space3353_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 131, 64, 34, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 259), (131, 327), (64, 325), (34, 280), (17, 184), (10, 168), (6, 256)]
    (codeMat 93) (codeMat 247) (codeMat 379) false
    det93 det247 inv247
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3353_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 34, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space3353_orbit
  simpa only [lower10] using h

theorem space3354_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 65, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 160), (129, 240), (65, 40), (33, 68), (17, 198), (10, 197), (6, 128)]
    (codeMat 107) (codeMat 465) (codeMat 465) false
    det107 det465 inv465
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3354_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space3354_orbit
  simpa only [lower11] using h

theorem space3355_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 139), (130, 9), (67, 119), (34, 136), (18, 8), (10, 392), (7, 360)]
    (codeMat 158) (codeMat 111) (codeMat 412) false
    det158 det111 inv111
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3355_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3355_orbit
  simpa only [lower14] using h

theorem space3356_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 66, 35, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 324), (130, 325), (66, 327), (35, 416), (17, 168), (10, 184), (4, 256)]
    (codeMat 92) (codeMat 459) (codeMat 346) false
    det92 det459 inv459
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3356_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 35, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space3356_orbit
  simpa only [lower10] using h

theorem space3357_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [258, 147, 66, 34, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(258, 344), (147, 269), (66, 350), (34, 336), (10, 343), (5, 5)]
    (codeMat 478) (codeMat 185) (codeMat 481) true
    det478 det185 inv185
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3357_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 147, 66, 34, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 25 space3357_orbit
  simpa only [lower25] using h

theorem space3358_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 66, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 196), (129, 71), (66, 70), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 93) (codeMat 474) (codeMat 395) false
    det93 det474 inv474
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3358_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3358_orbit
  simpa only [lower11] using h

theorem space3359_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 65, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 228), (130, 63), (65, 54), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 94) (codeMat 474) (codeMat 395) false
    det94 det474 inv474
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3359_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3359_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
