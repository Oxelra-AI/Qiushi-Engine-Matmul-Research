import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3392_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 68, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (128, 2), (68, 196), (36, 216), (20, 208), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    det84 det116 inv116
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3392_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3392_orbit
  simpa only [lower3] using h

theorem space3393_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 132, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (132, 70), (68, 68), (32, 8), (20, 112), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    det84 det212 inv212
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3393_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3393_orbit
  simpa only [lower3] using h

theorem space3394_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [274, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(274, 283), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    det273 det275 inv275
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space3394_lower : 18 ≤ frozenWangTable.L0 (spanCodes [274, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 426 space3394_orbit
  simpa only [lower426] using h

theorem space3395_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [259, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(259, 272), (16, 1), (10, 11)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    det266 det267 inv267
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space3395_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 426 space3395_orbit
  simpa only [lower426] using h

theorem space3396_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [262, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(262, 126), (21, 20), (10, 30)]
    (codeMat 467) (codeMat 213) (codeMat 470) false
    det467 det213 inv213
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3396_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3396_orbit
  simpa only [lower454] using h

theorem space3397_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [261, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(261, 191), (22, 20), (10, 30)]
    (codeMat 275) (codeMat 241) (codeMat 489) false
    det275 det241 inv241
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3397_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3397_orbit
  simpa only [lower456] using h

theorem space3398_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 106), (33, 10), (10, 30)]
    (codeMat 345) (codeMat 143) (codeMat 482) false
    det345 det143 inv143
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3398_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3398_orbit
  simpa only [lower454] using h

theorem space3399_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [275, 35, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(275, 181), (35, 10), (10, 30)]
    (codeMat 267) (codeMat 234) (codeMat 461) false
    det267 det234 inv234
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3399_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 35, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3399_orbit
  simpa only [lower456] using h

theorem space3400_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 37, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 116), (37, 10), (10, 30)]
    (codeMat 337) (codeMat 157) (codeMat 486) false
    det337 det157 inv157
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3400_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 37, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3400_orbit
  simpa only [lower454] using h

theorem space3401_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [275, 38, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(275, 171), (38, 10), (10, 30)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    det266 det122 inv122
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3401_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 38, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3401_orbit
  simpa only [lower456] using h

theorem space3402_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 116), (49, 20), (10, 30)]
    (codeMat 459) (codeMat 206) (codeMat 498) false
    det459 det206 inv206
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3402_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3402_orbit
  simpa only [lower454] using h

theorem space3403_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 52, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 106), (52, 10), (10, 30)]
    (codeMat 394) (codeMat 94) (codeMat 500) false
    det394 det94 inv94
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3403_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 52, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3403_orbit
  simpa only [lower454] using h

theorem space3404_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [275, 69, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(275, 253), (69, 78), (10, 68)]
    (codeMat 177) (codeMat 421) (codeMat 179) false
    det177 det421 inv421
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space3404_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 69, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space3404_orbit
  simpa only [lower463] using h

theorem space3405_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 70, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 314), (70, 10), (10, 68)]
    (codeMat 169) (codeMat 421) (codeMat 179) false
    det169 det421 inv421
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3405_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 70, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3405_orbit
  simpa only [lower465] using h

theorem space3406_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 71, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 382), (71, 10), (10, 68)]
    (codeMat 233) (codeMat 423) (codeMat 181) false
    det233 det423 inv423
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3406_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 71, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3406_orbit
  simpa only [lower465] using h

theorem space3407_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 80, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 106), (80, 10), (10, 30)]
    (codeMat 372) (codeMat 271) (codeMat 314) true
    det372 det271 inv271
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3407_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 80, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3407_orbit
  simpa only [lower454] using h

theorem space3408_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 81, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 116), (81, 20), (10, 30)]
    (codeMat 380) (codeMat 285) (codeMat 317) true
    det380 det285 inv285
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3408_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 81, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3408_orbit
  simpa only [lower454] using h

theorem space3409_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [275, 82, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(275, 181), (82, 10), (10, 30)]
    (codeMat 423) (codeMat 281) (codeMat 281) true
    det423 det281 inv281
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3409_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 82, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3409_orbit
  simpa only [lower456] using h

theorem space3410_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 85, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 94), (85, 342), (10, 258)]
    (codeMat 107) (codeMat 188) (codeMat 103) false
    det107 det188 inv188
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3410_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 85, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3410_orbit
  simpa only [lower469] using h

theorem space3411_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 87, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 379), (87, 94), (10, 10)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    det401 det277 inv277
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3411_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 87, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3411_orbit
  simpa only [lower473] using h

theorem space3412_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 97, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (97, 276), (10, 96)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    det86 det354 inv354
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3412_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 97, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3412_orbit
  simpa only [lower476] using h

theorem space3413_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 98, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 379), (98, 303), (10, 293)]
    (codeMat 370) (codeMat 161) (codeMat 161) false
    det370 det161 inv161
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3413_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 98, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3413_orbit
  simpa only [lower473] using h

theorem space3414_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 99, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 94), (99, 84), (10, 300)]
    (codeMat 470) (codeMat 485) (codeMat 171) false
    det470 det485 inv485
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3414_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 99, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3414_orbit
  simpa only [lower474] using h

theorem space3415_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 100, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 94), (100, 240), (10, 164)]
    (codeMat 253) (codeMat 348) (codeMat 125) false
    det253 det348 inv348
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3415_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 100, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space3415_orbit
  simpa only [lower468] using h

theorem space3416_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 101, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 286), (101, 276), (10, 96)]
    (codeMat 95) (codeMat 482) (codeMat 143) false
    det95 det482 inv482
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3416_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 101, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3416_orbit
  simpa only [lower476] using h

theorem space3417_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 102, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (102, 84), (10, 300)]
    (codeMat 415) (codeMat 359) (codeMat 174) false
    det415 det359 inv359
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3417_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 102, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3417_orbit
  simpa only [lower474] using h

theorem space3418_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 103, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 94), (103, 303), (10, 293)]
    (codeMat 379) (codeMat 163) (codeMat 165) false
    det379 det163 inv163
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3418_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 103, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3418_orbit
  simpa only [lower473] using h

theorem space3419_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 112, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (112, 10), (10, 276)]
    (codeMat 86) (codeMat 426) (codeMat 335) true
    det86 det426 inv426
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3419_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 112, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3419_orbit
  simpa only [lower476] using h

theorem space3420_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 114, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 84), (114, 94), (10, 294)]
    (codeMat 307) (codeMat 188) (codeMat 103) false
    det307 det188 inv188
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3420_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 114, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3420_orbit
  simpa only [lower474] using h

theorem space3421_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 115, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 299), (115, 94), (10, 383)]
    (codeMat 247) (codeMat 369) (codeMat 377) false
    det247 det369 inv369
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3421_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 115, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3421_orbit
  simpa only [lower471] using h

theorem space3422_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 117, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 106), (117, 286), (10, 276)]
    (codeMat 95) (codeMat 442) (codeMat 334) true
    det95 det442 inv442
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3422_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 117, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3422_orbit
  simpa only [lower476] using h

theorem space3423_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 118, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (118, 376), (10, 294)]
    (codeMat 314) (codeMat 172) (codeMat 99) false
    det314 det172 inv172
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3423_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 118, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3423_orbit
  simpa only [lower474] using h


end QiushiMatmul.FrozenWang
