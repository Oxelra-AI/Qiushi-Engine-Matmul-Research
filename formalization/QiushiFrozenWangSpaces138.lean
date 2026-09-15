import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4416_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 66, 33, 17, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 327), (130, 325), (66, 326), (33, 440), (17, 424), (9, 432), (7, 256)]
    (codeMat 84) (codeMat 494) (codeMat 501) false
    det84 det494 inv494
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4416_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 33, 17, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space4416_orbit
  simpa only [lower10] using h

theorem space4417_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 67, 32, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (131, 196), (67, 199), (32, 8), (16, 32), (11, 248), (7, 128)]
    (codeMat 84) (codeMat 205) (codeMat 242) false
    det84 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4417_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4417_orbit
  simpa only [lower11] using h

theorem space4418_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 67, 33, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (130, 3), (67, 199), (33, 112), (16, 216), (11, 248), (7, 128)]
    (codeMat 93) (codeMat 379) (codeMat 247) false
    det93 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4418_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4418_orbit
  simpa only [lower11] using h

theorem space4419_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 131, 65, 32, 16, 9, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 129), (131, 196), (65, 3), (32, 8), (16, 32), (9, 216), (5, 128)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    det85 det141 inv141
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4419_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 16, 9, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space4419_orbit
  simpa only [lower11] using h

theorem space4420_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 131, 64, 32, 17, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 136), (131, 240), (64, 216), (32, 1), (17, 198), (8, 3), (5, 128)]
    (codeMat 106) (codeMat 157) (codeMat 486) false
    det106 det157 inv157
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4420_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 17, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space4420_orbit
  simpa only [lower11] using h

theorem space4421_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 65, 33, 16, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 510), (130, 1), (65, 3), (33, 232), (16, 8), (11, 136), (5, 360)]
    (codeMat 213) (codeMat 299) (codeMat 318) false
    det213 det299 inv299
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4421_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 33, 16, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4421_orbit
  simpa only [lower14] using h

theorem space4422_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 19, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 29), (129, 22), (66, 20), (34, 373), (19, 406), (11, 276), (5, 8)]
    (codeMat 461) (codeMat 468) (codeMat 87) false
    det461 det468 inv468
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4422_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 19, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4422_orbit
  simpa only [lower14] using h

theorem space4423_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 67, 35, 18, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 276), (128, 130), (67, 381), (35, 28), (18, 2), (11, 21), (5, 8)]
    (codeMat 459) (codeMat 337) (codeMat 337) false
    det459 det337 inv337
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4423_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 35, 18, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4423_orbit
  simpa only [lower14] using h

theorem space4424_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 65, 35, 17, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 68), (128, 325), (65, 3), (35, 160), (17, 424), (9, 24), (4, 256)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    det93 det395 inv395
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4424_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 35, 17, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space4424_orbit
  simpa only [lower10] using h

theorem space4425_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 65, 33, 17, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 210), (130, 54), (65, 9), (33, 80), (17, 112), (8, 8), (4, 128)]
    (codeMat 87) (codeMat 177) (codeMat 417) false
    det87 det177 inv177
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4425_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 33, 17, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space4425_orbit
  simpa only [lower11] using h

theorem space4426_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 64, 35, 16, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 68), (128, 1), (64, 3), (35, 160), (16, 8), (8, 24), (4, 256)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    det84 det267 inv267
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4426_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 35, 16, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space4426_orbit
  simpa only [lower10] using h

theorem space4427_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 67, 35, 19, 11, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 68), (128, 325), (67, 327), (35, 160), (19, 168), (11, 184), (4, 256)]
    (codeMat 85) (codeMat 459) (codeMat 346) false
    det85 det459 inv459
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4427_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 35, 19, 11, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space4427_orbit
  simpa only [lower10] using h

theorem space4428_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 66, 32, 17, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 97), (131, 235), (66, 414), (32, 256), (17, 387), (9, 3), (7, 130)]
    (codeMat 171) (codeMat 395) (codeMat 474) false
    det171 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4428_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 66, 32, 17, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4428_orbit
  simpa only [lower14] using h

theorem space4429_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 32, 19, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 361), (64, 1), (32, 130), (19, 105), (9, 8), (7, 511)]
    (codeMat 412) (codeMat 161) (codeMat 161) false
    det412 det161 inv161
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4429_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 32, 19, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4429_orbit
  simpa only [lower14] using h

theorem space4430_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 64, 35, 19, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 352), (128, 384), (64, 128), (35, 361), (19, 150), (9, 2), (7, 360)]
    (codeMat 299) (codeMat 156) (codeMat 102) false
    det299 det156 inv156
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4430_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 35, 19, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4430_orbit
  simpa only [lower14] using h

theorem space4431_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 130, 65, 33, 18, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (130, 2), (65, 3), (33, 424), (18, 16), (9, 24), (7, 256)]
    (codeMat 93) (codeMat 285) (codeMat 317) false
    det93 det285 inv285
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4431_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 65, 33, 18, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space4431_orbit
  simpa only [lower10] using h

theorem space4432_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 32, 18, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 381), (131, 406), (65, 130), (32, 360), (18, 384), (9, 128), (7, 8)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    det206 det412 inv412
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4432_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 18, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4432_orbit
  simpa only [lower14] using h

theorem space4433_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 33, 16, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 363), (130, 2), (67, 148), (33, 480), (16, 128), (8, 256), (7, 360)]
    (codeMat 157) (codeMat 116) (codeMat 92) false
    det157 det116 inv116
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4433_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 33, 16, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4433_orbit
  simpa only [lower14] using h

theorem space4434_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 65, 33, 18, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 361), (130, 2), (65, 1), (33, 105), (18, 130), (8, 8), (7, 511)]
    (codeMat 405) (codeMat 273) (codeMat 273) false
    det405 det273 inv273
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4434_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 33, 18, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4434_orbit
  simpa only [lower14] using h

theorem space4435_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 65, 35, 18, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (128, 2), (65, 325), (35, 280), (18, 16), (11, 168), (7, 256)]
    (codeMat 92) (codeMat 117) (codeMat 380) false
    det92 det117 inv117
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4435_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 35, 18, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space4435_orbit
  simpa only [lower10] using h

theorem space4436_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 28), (67, 31), (32, 128), (16, 256), (10, 480), (7, 8)]
    (codeMat 140) (codeMat 233) (codeMat 233) false
    det140 det233 inv233
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4436_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4436_orbit
  simpa only [lower14] using h

theorem space4437_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 65, 33, 19, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (130, 256), (65, 128), (33, 381), (19, 276), (9, 130), (6, 8)]
    (codeMat 334) (codeMat 396) (codeMat 106) false
    det334 det396 inv396
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4437_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 65, 33, 19, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space4437_orbit
  simpa only [lower14] using h

theorem space4438_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 128, 64, 35, 18, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 71), (128, 3), (64, 2), (35, 440), (18, 24), (9, 16), (6, 256)]
    (codeMat 92) (codeMat 318) (codeMat 299) false
    det92 det318 inv318
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4438_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 35, 18, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4438_orbit
  simpa only [lower10] using h

theorem space4439_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 34, 18, 8, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 373), (129, 97), (64, 8), (34, 258), (18, 256), (8, 1), (6, 130)]
    (codeMat 226) (codeMat 417) (codeMat 177) false
    det226 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4439_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 34, 18, 8, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space4439_orbit
  simpa only [lower14] using h

theorem space4440_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 129, 66, 34, 16, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 258), (129, 70), (66, 71), (34, 272), (16, 432), (11, 440), (6, 256)]
    (codeMat 93) (codeMat 249) (codeMat 425) false
    det93 det249 inv249
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4440_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 16, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4440_orbit
  simpa only [lower10] using h

theorem space4441_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 132, 70, 38, 18, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 287), (132, 252), (70, 278), (38, 284), (18, 511), (14, 276), (1, 130)]
    (codeMat 470) (codeMat 190) (codeMat 355) false
    det470 det190 inv190
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4441_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 132, 70, 38, 18, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4441_orbit
  simpa only [lower14] using h

theorem space4442_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 128, 68, 34, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (128, 2), (68, 324), (34, 168), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    det84 det340 inv340
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4442_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 34, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4442_orbit
  simpa only [lower10] using h

theorem space4443_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 72, 34, 24, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 170), (128, 325), (72, 1), (34, 168), (24, 256), (4, 16), (1, 8)]
    (codeMat 142) (codeMat 163) (codeMat 165) false
    det142 det163 inv163
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4443_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 72, 34, 24, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4443_orbit
  simpa only [lower10] using h

theorem space4444_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [264, 136, 74, 42, 26, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(264, 68), (136, 198), (74, 53), (42, 112), (26, 240), (4, 32), (1, 40)]
    (codeMat 142) (codeMat 465) (codeMat 465) false
    det142 det465 inv465
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4444_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 136, 74, 42, 26, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4444_orbit
  simpa only [lower11] using h

theorem space4445_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 128, 66, 34, 18, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 404), (128, 9), (66, 118), (34, 352), (18, 8), (4, 256), (1, 384)]
    (codeMat 95) (codeMat 330) (codeMat 394) false
    det95 det330 inv330
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4445_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 128, 66, 34, 18, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4445_orbit
  simpa only [lower14] using h

theorem space4446_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 146, 82, 48, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 440), (146, 511), (82, 255), (48, 1), (8, 3), (6, 8), (1, 24)]
    (codeMat 266) (codeMat 443) (codeMat 254) false
    det266 det443 inv443
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4446_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 146, 82, 48, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4446_orbit
  simpa only [lower10] using h

theorem space4447_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [257, 135, 70, 36, 18, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(257, 344), (135, 88), (70, 264), (36, 6), (18, 2), (9, 5)]
    (codeMat 355) (codeMat 369) (codeMat 377) false
    det355 det369 inv369
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4447_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 135, 70, 36, 18, 9]) := by
  have h := frozenWangTable.lower_le_L0 25 space4447_orbit
  simpa only [lower25] using h


end QiushiMatmul.FrozenWang
