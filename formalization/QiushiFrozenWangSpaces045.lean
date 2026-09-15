import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1440_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 361), (131, 363), (64, 3), (35, 105), (19, 235), (10, 373), (5, 511)]
    (codeMat 412) (codeMat 409) (codeMat 473) false
    det412 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1440_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1440_orbit
  simpa only [lower14] using h

theorem space1441_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 386), (128, 3), (65, 384), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 348) (codeMat 346) (codeMat 459) false
    det348 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1441_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1441_orbit
  simpa only [lower14] using h

theorem space1442_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (129, 232), (65, 360), (35, 276), (19, 235), (10, 373), (5, 8)]
    (codeMat 271) (codeMat 339) (codeMat 467) false
    det271 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1442_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1442_orbit
  simpa only [lower14] using h

theorem space1443_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 245), (66, 413), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 470) (codeMat 157) (codeMat 486) false
    det470 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1443_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1443_orbit
  simpa only [lower14] using h

theorem space1444_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 31), (131, 29), (67, 30), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 460) (codeMat 494) (codeMat 501) false
    det460 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1444_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1444_orbit
  simpa only [lower14] using h

theorem space1445_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (67, 363), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 468) (codeMat 94) (codeMat 500) false
    det468 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1445_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1445_orbit
  simpa only [lower14] using h

theorem space1446_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 509), (130, 3), (64, 360), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 477) (codeMat 115) (codeMat 492) false
    det477 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1446_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1446_orbit
  simpa only [lower14] using h

theorem space1447_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 126), (129, 245), (64, 360), (32, 511), (19, 373), (10, 235), (5, 130)]
    (codeMat 478) (codeMat 501) (codeMat 494) false
    det478 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1447_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1447_orbit
  simpa only [lower14] using h

theorem space1448_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 10), (131, 29), (65, 3), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 461) (codeMat 171) (codeMat 485) false
    det461 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1448_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1448_orbit
  simpa only [lower14] using h

theorem space1449_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 259), (130, 3), (66, 387), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 277) (codeMat 375) (codeMat 491) false
    det277 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1449_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1449_orbit
  simpa only [lower14] using h

theorem space1450_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (66, 246), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 279) (codeMat 241) (codeMat 489) false
    det279 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1450_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1450_orbit
  simpa only [lower14] using h

theorem space1451_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 23), (130, 3), (67, 30), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 461) (codeMat 382) (codeMat 499) false
    det461 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1451_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1451_orbit
  simpa only [lower14] using h

theorem space1452_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 510), (128, 360), (67, 363), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 477) (codeMat 206) (codeMat 498) false
    det477 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1452_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1452_orbit
  simpa only [lower14] using h

theorem space1453_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 509), (131, 363), (64, 360), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 405) (codeMat 241) (codeMat 489) false
    det405 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1453_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1453_orbit
  simpa only [lower14] using h

theorem space1454_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 126), (129, 413), (64, 360), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 407) (codeMat 375) (codeMat 491) false
    det407 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1454_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1454_orbit
  simpa only [lower14] using h

theorem space1455_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 246), (65, 384), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 351) (codeMat 206) (codeMat 498) false
    det351 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1455_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1455_orbit
  simpa only [lower14] using h

theorem space1456_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 480), (129, 232), (65, 384), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 335) (codeMat 382) (codeMat 499) false
    det335 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1456_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1456_orbit
  simpa only [lower14] using h

theorem space1457_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [292, 129, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(292, 4), (129, 210), (65, 9), (17, 80), (8, 8), (2, 128)]
    (codeMat 87) (codeMat 273) (codeMat 273) false
    det87 det273 inv273
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1457_lower : 12 ≤ frozenWangTable.L0 (spanCodes [292, 129, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1457_orbit
  simpa only [lower23] using h

theorem space1458_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 68, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    det92 det204 inv204
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1458_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1458_orbit
  simpa only [lower10] using h

theorem space1459_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 69, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (133, 324), (69, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    det92 det236 inv236
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1459_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 69, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1459_orbit
  simpa only [lower10] using h

theorem space1460_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 65, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 126), (132, 245), (65, 9), (36, 384), (17, 96), (8, 8), (2, 360)]
    (codeMat 215) (codeMat 419) (codeMat 183) false
    det215 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1460_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 65, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1460_orbit
  simpa only [lower14] using h

theorem space1461_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 68, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 105), (132, 227), (68, 97), (37, 361), (17, 149), (8, 360), (2, 511)]
    (codeMat 491) (codeMat 467) (codeMat 339) false
    det491 det467 inv467
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1461_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1461_orbit
  simpa only [lower14] using h

theorem space1462_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 69, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (132, 68), (69, 326), (37, 424), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 460) (codeMat 122) false
    det93 det460 inv460
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1462_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 69, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1462_orbit
  simpa only [lower10] using h

theorem space1463_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 69, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 235), (133, 284), (69, 414), (37, 363), (17, 149), (8, 360), (2, 511)]
    (codeMat 491) (codeMat 499) (codeMat 382) false
    det491 det499 inv499
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1463_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 69, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1463_orbit
  simpa only [lower14] using h

theorem space1464_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 69, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 3), (128, 9), (69, 29), (37, 232), (17, 96), (8, 360), (2, 8)]
    (codeMat 205) (codeMat 103) (codeMat 188) false
    det205 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1464_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 69, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1464_orbit
  simpa only [lower14] using h

theorem space1465_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 119), (133, 245), (65, 9), (37, 392), (17, 96), (8, 8), (2, 360)]
    (codeMat 215) (codeMat 423) (codeMat 181) false
    det215 det423 inv423
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1465_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1465_orbit
  simpa only [lower14] using h

theorem space1466_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 69, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 278), (132, 245), (69, 404), (32, 384), (17, 96), (8, 256), (2, 360)]
    (codeMat 158) (codeMat 482) (codeMat 143) false
    det158 det482 inv482
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1466_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 69, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1466_orbit
  simpa only [lower14] using h

theorem space1467_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 64, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (132, 68), (64, 2), (32, 8), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    det84 det140 inv140
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1467_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1467_orbit
  simpa only [lower10] using h

theorem space1468_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 128, 65, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 68), (128, 130), (65, 1), (32, 32), (17, 80), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    det85 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1468_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1468_orbit
  simpa only [lower11] using h

theorem space1469_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 406), (132, 227), (64, 130), (33, 150), (17, 149), (8, 2), (2, 511)]
    (codeMat 426) (codeMat 410) (codeMat 331) false
    det426 det410 inv410
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1469_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1469_orbit
  simpa only [lower14] using h

theorem space1470_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 65, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (132, 68), (65, 2), (33, 168), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 396) (codeMat 106) false
    det85 det396 inv396
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1470_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 65, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1470_orbit
  simpa only [lower10] using h

theorem space1471_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 133, 65, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 327), (133, 68), (65, 2), (33, 184), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 428) (codeMat 107) false
    det85 det428 inv428
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1471_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1471_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
