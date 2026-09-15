import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1504_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 150), (128, 360), (67, 363), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 477) (codeMat 458) (codeMat 458) false
    det477 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1504_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1504_orbit
  simpa only [lower14] using h

theorem space1505_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 361), (130, 360), (66, 363), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 412) (codeMat 458) (codeMat 458) false
    det412 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1505_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1505_orbit
  simpa only [lower14] using h

theorem space1506_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (66, 246), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 279) (codeMat 465) (codeMat 465) false
    det279 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1506_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1506_orbit
  simpa only [lower14] using h

theorem space1507_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 30), (67, 29), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 396) (codeMat 241) (codeMat 489) false
    det396 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1507_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1507_orbit
  simpa only [lower14] using h

theorem space1508_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 23), (130, 3), (67, 29), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 397) (codeMat 375) (codeMat 491) false
    det397 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1508_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1508_orbit
  simpa only [lower14] using h

theorem space1509_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 10), (129, 30), (66, 29), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 461) (codeMat 241) (codeMat 489) false
    det461 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1509_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1509_orbit
  simpa only [lower14] using h

theorem space1510_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 31), (128, 3), (66, 29), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 460) (codeMat 375) (codeMat 491) false
    det460 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1510_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1510_orbit
  simpa only [lower14] using h

theorem space1511_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (129, 387), (65, 384), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 340) (codeMat 206) (codeMat 498) false
    det340 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1511_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1511_orbit
  simpa only [lower14] using h

theorem space1512_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 385), (128, 3), (65, 384), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 348) (codeMat 382) (codeMat 499) false
    det348 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1512_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1512_orbit
  simpa only [lower14] using h

theorem space1513_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 131), (131, 387), (64, 384), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 277) (codeMat 206) (codeMat 498) false
    det277 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1513_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1513_orbit
  simpa only [lower14] using h

theorem space1514_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 259), (130, 3), (64, 384), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 285) (codeMat 382) (codeMat 499) false
    det285 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1514_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1514_orbit
  simpa only [lower14] using h

theorem space1515_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 31), (131, 30), (67, 29), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 396) (codeMat 501) (codeMat 494) false
    det396 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1515_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1515_orbit
  simpa only [lower14] using h

theorem space1516_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 10), (130, 3), (67, 29), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 397) (codeMat 115) (codeMat 492) false
    det397 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1516_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1516_orbit
  simpa only [lower14] using h

theorem space1517_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 413), (66, 245), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 415) (codeMat 94) (codeMat 500) false
    det415 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1517_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1517_orbit
  simpa only [lower14] using h

theorem space1518_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 126), (128, 360), (66, 245), (34, 381), (19, 235), (10, 373), (6, 130)]
    (codeMat 407) (codeMat 494) (codeMat 501) false
    det407 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1518_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1518_orbit
  simpa only [lower14] using h

theorem space1519_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 509), (128, 360), (65, 3), (34, 381), (19, 414), (10, 373), (6, 511)]
    (codeMat 405) (codeMat 171) (codeMat 485) false
    det405 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1519_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1519_orbit
  simpa only [lower14] using h

theorem space1520_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (131, 363), (64, 3), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 412) (codeMat 157) (codeMat 486) false
    det412 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1520_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1520_orbit
  simpa only [lower14] using h

theorem space1521_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (131, 374), (67, 246), (33, 105), (19, 373), (10, 414), (6, 511)]
    (codeMat 286) (codeMat 339) (codeMat 467) false
    det286 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1521_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1521_orbit
  simpa only [lower14] using h

theorem space1522_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 361), (128, 3), (67, 363), (33, 406), (19, 373), (10, 235), (6, 511)]
    (codeMat 468) (codeMat 346) (codeMat 459) false
    det468 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1522_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1522_orbit
  simpa only [lower14] using h

theorem space1523_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (130, 360), (66, 232), (33, 284), (19, 373), (10, 235), (6, 8)]
    (codeMat 270) (codeMat 395) (codeMat 474) false
    det270 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1523_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1523_orbit
  simpa only [lower14] using h

theorem space1524_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 353), (129, 245), (66, 413), (33, 227), (19, 373), (10, 414), (6, 130)]
    (codeMat 470) (codeMat 409) (codeMat 473) false
    det470 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1524_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1524_orbit
  simpa only [lower14] using h

theorem space1525_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 255), (131, 374), (65, 384), (33, 406), (19, 373), (10, 235), (6, 511)]
    (codeMat 342) (codeMat 346) (codeMat 459) false
    det342 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1525_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1525_orbit
  simpa only [lower14] using h

theorem space1526_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 361), (128, 3), (65, 360), (33, 105), (19, 373), (10, 414), (6, 511)]
    (codeMat 412) (codeMat 339) (codeMat 467) false
    det412 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1526_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1526_orbit
  simpa only [lower14] using h

theorem space1527_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 386), (130, 384), (64, 3), (33, 227), (19, 373), (10, 414), (6, 130)]
    (codeMat 340) (codeMat 409) (codeMat 473) false
    det340 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1527_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1527_orbit
  simpa only [lower14] using h

theorem space1528_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 28), (129, 29), (64, 3), (33, 284), (19, 373), (10, 235), (6, 8)]
    (codeMat 396) (codeMat 395) (codeMat 474) false
    det396 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1528_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1528_orbit
  simpa only [lower14] using h

theorem space1529_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 384), (67, 246), (32, 8), (19, 235), (10, 414), (6, 511)]
    (codeMat 342) (codeMat 213) (codeMat 470) false
    det342 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1529_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1529_orbit
  simpa only [lower14] using h

theorem space1530_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 509), (128, 360), (67, 363), (32, 130), (19, 414), (10, 235), (6, 511)]
    (codeMat 477) (codeMat 234) (codeMat 461) false
    det477 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1530_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1530_orbit
  simpa only [lower14] using h

theorem space1531_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 480), (130, 384), (66, 232), (32, 511), (19, 414), (10, 235), (6, 8)]
    (codeMat 334) (codeMat 445) (codeMat 478) false
    det334 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1531_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1531_orbit
  simpa only [lower14] using h

theorem space1532_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 126), (128, 360), (66, 413), (32, 511), (19, 235), (10, 414), (6, 130)]
    (codeMat 478) (codeMat 431) (codeMat 477) false
    det478 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1532_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1532_orbit
  simpa only [lower14] using h

theorem space1533_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 23), (131, 30), (65, 3), (32, 511), (19, 414), (10, 235), (6, 8)]
    (codeMat 397) (codeMat 445) (codeMat 478) false
    det397 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1533_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1533_orbit
  simpa only [lower14] using h

theorem space1534_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 259), (129, 387), (65, 3), (32, 511), (19, 235), (10, 414), (6, 130)]
    (codeMat 285) (codeMat 431) (codeMat 477) false
    det285 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1534_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1534_orbit
  simpa only [lower14] using h

theorem space1535_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 510), (131, 363), (64, 360), (32, 8), (19, 235), (10, 414), (6, 511)]
    (codeMat 405) (codeMat 213) (codeMat 470) false
    det405 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1535_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1535_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
