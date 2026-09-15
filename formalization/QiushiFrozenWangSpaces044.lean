import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1408_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 126), (131, 413), (67, 245), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 478) (codeMat 382) (codeMat 499) false
    det478 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1408_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1408_orbit
  simpa only [lower14] using h

theorem space1409_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 136), (130, 384), (64, 360), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 335) (codeMat 241) (codeMat 489) false
    det335 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1409_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1409_orbit
  simpa only [lower14] using h

theorem space1410_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 480), (131, 232), (64, 360), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 334) (codeMat 375) (codeMat 491) false
    det334 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1410_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1410_orbit
  simpa only [lower14] using h

theorem space1411_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (65, 360), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 270) (codeMat 241) (codeMat 489) false
    det270 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1411_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1411_orbit
  simpa only [lower14] using h

theorem space1412_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 488), (129, 232), (65, 360), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 271) (codeMat 375) (codeMat 491) false
    det271 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1412_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1412_orbit
  simpa only [lower14] using h

theorem space1413_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (130, 384), (66, 387), (34, 276), (19, 373), (10, 235), (4, 130)]
    (codeMat 348) (codeMat 241) (codeMat 489) false
    det348 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1413_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1413_orbit
  simpa only [lower14] using h

theorem space1414_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 393), (129, 374), (66, 246), (34, 284), (19, 373), (10, 414), (4, 511)]
    (codeMat 351) (codeMat 375) (codeMat 491) false
    det351 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1414_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1414_orbit
  simpa only [lower14] using h

theorem space1415_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (131, 29), (67, 30), (34, 97), (19, 373), (10, 414), (4, 8)]
    (codeMat 460) (codeMat 206) (codeMat 498) false
    det460 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1415_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1415_orbit
  simpa only [lower14] using h

theorem space1416_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 362), (128, 3), (67, 363), (34, 227), (19, 373), (10, 235), (4, 511)]
    (codeMat 468) (codeMat 382) (codeMat 499) false
    det468 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1416_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1416_orbit
  simpa only [lower14] using h

theorem space1417_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 104), (130, 360), (64, 384), (34, 97), (19, 373), (10, 414), (4, 8)]
    (codeMat 271) (codeMat 206) (codeMat 498) false
    det271 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1417_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1417_orbit
  simpa only [lower14] using h

theorem space1418_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 118), (129, 374), (64, 384), (34, 227), (19, 373), (10, 235), (4, 511)]
    (codeMat 279) (codeMat 382) (codeMat 499) false
    det279 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1418_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1418_orbit
  simpa only [lower14] using h

theorem space1419_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 404), (131, 245), (65, 360), (34, 276), (19, 373), (10, 235), (4, 130)]
    (codeMat 415) (codeMat 241) (codeMat 489) false
    det415 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1419_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1419_orbit
  simpa only [lower14] using h

theorem space1420_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 362), (128, 3), (65, 360), (34, 284), (19, 373), (10, 414), (4, 511)]
    (codeMat 412) (codeMat 375) (codeMat 491) false
    det412 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1420_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1420_orbit
  simpa only [lower14] using h

theorem space1421_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 278), (128, 360), (66, 413), (35, 276), (19, 235), (10, 414), (4, 130)]
    (codeMat 478) (codeMat 171) (codeMat 485) false
    det478 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1421_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1421_orbit
  simpa only [lower14] using h

theorem space1422_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 3), (67, 30), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 461) (codeMat 94) (codeMat 500) false
    det461 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1422_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1422_orbit
  simpa only [lower14] using h

theorem space1423_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 149), (128, 360), (67, 363), (35, 284), (19, 414), (10, 235), (4, 511)]
    (codeMat 477) (codeMat 494) (codeMat 501) false
    det477 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1423_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1423_orbit
  simpa only [lower14] using h

theorem space1424_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (129, 30), (64, 3), (35, 97), (19, 414), (10, 235), (4, 8)]
    (codeMat 460) (codeMat 157) (codeMat 486) false
    det460 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1424_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1424_orbit
  simpa only [lower14] using h

theorem space1425_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 404), (131, 413), (65, 360), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 470) (codeMat 115) (codeMat 492) false
    det470 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1425_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1425_orbit
  simpa only [lower14] using h

theorem space1426_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 362), (129, 363), (65, 360), (35, 227), (19, 235), (10, 414), (4, 511)]
    (codeMat 468) (codeMat 501) (codeMat 494) false
    det468 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1426_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1426_orbit
  simpa only [lower14] using h

theorem space1427_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 278), (128, 360), (66, 245), (33, 406), (19, 235), (10, 373), (4, 130)]
    (codeMat 407) (codeMat 234) (codeMat 461) false
    det407 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1427_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1427_orbit
  simpa only [lower14] using h

theorem space1428_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 30), (66, 29), (33, 105), (19, 414), (10, 373), (4, 8)]
    (codeMat 461) (codeMat 213) (codeMat 470) false
    det461 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1428_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1428_orbit
  simpa only [lower14] using h

theorem space1429_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 393), (130, 384), (67, 374), (33, 284), (19, 235), (10, 373), (4, 511)]
    (codeMat 351) (codeMat 445) (codeMat 478) false
    det351 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1429_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1429_orbit
  simpa only [lower14] using h

theorem space1430_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 118), (131, 246), (67, 374), (33, 227), (19, 414), (10, 373), (4, 511)]
    (codeMat 279) (codeMat 431) (codeMat 477) false
    det279 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1430_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1430_orbit
  simpa only [lower14] using h

theorem space1431_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 96), (130, 384), (64, 360), (33, 105), (19, 414), (10, 373), (4, 8)]
    (codeMat 335) (codeMat 213) (codeMat 470) false
    det335 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1431_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1431_orbit
  simpa only [lower14] using h

theorem space1432_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (131, 387), (64, 384), (33, 406), (19, 235), (10, 373), (4, 130)]
    (codeMat 277) (codeMat 234) (codeMat 461) false
    det277 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1432_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1432_orbit
  simpa only [lower14] using h

theorem space1433_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 149), (128, 360), (65, 3), (33, 227), (19, 414), (10, 373), (4, 511)]
    (codeMat 405) (codeMat 431) (codeMat 477) false
    det405 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1433_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1433_orbit
  simpa only [lower14] using h

theorem space1434_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 149), (129, 363), (65, 3), (33, 284), (19, 235), (10, 373), (4, 511)]
    (codeMat 477) (codeMat 445) (codeMat 478) false
    det477 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1434_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1434_orbit
  simpa only [lower14] using h

theorem space1435_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 28), (128, 3), (66, 29), (35, 276), (19, 235), (10, 373), (5, 8)]
    (codeMat 460) (codeMat 339) (codeMat 467) false
    det460 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1435_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1435_orbit
  simpa only [lower14] using h

theorem space1436_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 353), (129, 413), (66, 245), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 415) (codeMat 346) (codeMat 459) false
    det415 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1436_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1436_orbit
  simpa only [lower14] using h

theorem space1437_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 255), (130, 384), (67, 374), (35, 105), (19, 235), (10, 373), (5, 511)]
    (codeMat 351) (codeMat 409) (codeMat 473) false
    det351 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1437_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1437_orbit
  simpa only [lower14] using h

theorem space1438_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (131, 246), (67, 374), (35, 406), (19, 414), (10, 373), (5, 511)]
    (codeMat 279) (codeMat 395) (codeMat 474) false
    det279 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1438_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1438_orbit
  simpa only [lower14] using h

theorem space1439_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 361), (130, 360), (64, 3), (35, 406), (19, 414), (10, 373), (5, 511)]
    (codeMat 468) (codeMat 395) (codeMat 474) false
    det468 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1439_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1439_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
