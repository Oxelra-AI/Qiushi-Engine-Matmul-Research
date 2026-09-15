import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1312_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 404), (130, 360), (67, 413), (35, 276), (19, 235), (10, 414), (4, 130)]
    (codeMat 415) (codeMat 171) (codeMat 485) false
    det415 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1312_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1312_orbit
  simpa only [lower14] using h

theorem space1313_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (66, 30), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 396) (codeMat 94) (codeMat 500) false
    det396 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1313_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1313_orbit
  simpa only [lower14] using h

theorem space1314_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 362), (130, 360), (66, 363), (35, 284), (19, 414), (10, 235), (4, 511)]
    (codeMat 412) (codeMat 494) (codeMat 501) false
    det412 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1314_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1314_orbit
  simpa only [lower14] using h

theorem space1315_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 96), (128, 360), (65, 384), (34, 97), (19, 373), (10, 414), (4, 8)]
    (codeMat 334) (codeMat 206) (codeMat 498) false
    det334 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1315_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1315_orbit
  simpa only [lower14] using h

theorem space1316_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 393), (131, 374), (65, 384), (34, 227), (19, 373), (10, 235), (4, 511)]
    (codeMat 342) (codeMat 382) (codeMat 499) false
    det342 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1316_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1316_orbit
  simpa only [lower14] using h

theorem space1317_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 278), (129, 245), (64, 360), (34, 276), (19, 373), (10, 235), (4, 130)]
    (codeMat 478) (codeMat 241) (codeMat 489) false
    det478 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1317_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1317_orbit
  simpa only [lower14] using h

theorem space1318_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 149), (130, 3), (64, 360), (34, 284), (19, 373), (10, 414), (4, 511)]
    (codeMat 477) (codeMat 375) (codeMat 491) false
    det477 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1318_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1318_orbit
  simpa only [lower14] using h

theorem space1319_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (67, 387), (34, 276), (19, 373), (10, 235), (4, 130)]
    (codeMat 285) (codeMat 241) (codeMat 489) false
    det285 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1319_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1319_orbit
  simpa only [lower14] using h

theorem space1320_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 118), (131, 374), (67, 246), (34, 284), (19, 373), (10, 414), (4, 511)]
    (codeMat 286) (codeMat 375) (codeMat 491) false
    det286 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1320_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1320_orbit
  simpa only [lower14] using h

theorem space1321_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 29), (66, 30), (34, 97), (19, 373), (10, 414), (4, 8)]
    (codeMat 397) (codeMat 206) (codeMat 498) false
    det397 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1321_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1321_orbit
  simpa only [lower14] using h

theorem space1322_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 149), (130, 3), (66, 363), (34, 227), (19, 373), (10, 235), (4, 511)]
    (codeMat 405) (codeMat 382) (codeMat 499) false
    det405 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1322_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1322_orbit
  simpa only [lower14] using h

theorem space1323_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 510), (128, 360), (65, 3), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 405) (codeMat 143) (codeMat 482) false
    det405 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1323_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1323_orbit
  simpa only [lower14] using h

theorem space1324_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (130, 360), (64, 3), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 468) (codeMat 143) (codeMat 482) false
    det468 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1324_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1324_orbit
  simpa only [lower14] using h

theorem space1325_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 383), (130, 384), (67, 374), (32, 130), (19, 235), (10, 373), (7, 511)]
    (codeMat 351) (codeMat 185) (codeMat 481) false
    det351 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1325_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1325_orbit
  simpa only [lower14] using h

theorem space1326_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (66, 374), (32, 130), (19, 235), (10, 373), (7, 511)]
    (codeMat 286) (codeMat 185) (codeMat 481) false
    det286 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1326_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1326_orbit
  simpa only [lower14] using h

theorem space1327_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (65, 360), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 412) (codeMat 87) (codeMat 468) false
    det412 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1327_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1327_orbit
  simpa only [lower14] using h

theorem space1328_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 383), (131, 374), (65, 384), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 342) (codeMat 122) (codeMat 460) false
    det342 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1328_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1328_orbit
  simpa only [lower14] using h

theorem space1329_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (129, 374), (64, 384), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 279) (codeMat 122) (codeMat 460) false
    det279 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1329_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1329_orbit
  simpa only [lower14] using h

theorem space1330_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 510), (130, 3), (64, 360), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 477) (codeMat 87) (codeMat 468) false
    det477 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1330_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1330_orbit
  simpa only [lower14] using h

theorem space1331_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (129, 387), (65, 3), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 285) (codeMat 395) (codeMat 474) false
    det285 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1331_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1331_orbit
  simpa only [lower14] using h

theorem space1332_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 20), (131, 30), (65, 3), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 397) (codeMat 409) (codeMat 473) false
    det397 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1332_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1332_orbit
  simpa only [lower14] using h

theorem space1333_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 28), (129, 30), (64, 3), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 460) (codeMat 409) (codeMat 473) false
    det460 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1333_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1333_orbit
  simpa only [lower14] using h

theorem space1334_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 386), (131, 387), (64, 3), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 348) (codeMat 395) (codeMat 474) false
    det348 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1334_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1334_orbit
  simpa only [lower14] using h

theorem space1335_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 386), (128, 3), (67, 387), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 340) (codeMat 339) (codeMat 467) false
    det340 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1335_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1335_orbit
  simpa only [lower14] using h

theorem space1336_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 20), (130, 3), (67, 30), (34, 284), (19, 235), (10, 414), (7, 8)]
    (codeMat 461) (codeMat 346) (codeMat 459) false
    det461 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1336_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1336_orbit
  simpa only [lower14] using h

theorem space1337_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 28), (128, 3), (66, 30), (34, 284), (19, 235), (10, 414), (7, 8)]
    (codeMat 396) (codeMat 346) (codeMat 459) false
    det396 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1337_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1337_orbit
  simpa only [lower14] using h

theorem space1338_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (130, 3), (66, 387), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 277) (codeMat 339) (codeMat 467) false
    det277 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1338_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1338_orbit
  simpa only [lower14] using h

theorem space1339_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 483), (129, 245), (64, 360), (33, 97), (19, 373), (10, 235), (6, 130)]
    (codeMat 478) (codeMat 465) (codeMat 465) false
    det478 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1339_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1339_orbit
  simpa only [lower14] using h

theorem space1340_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (130, 360), (64, 384), (33, 276), (19, 373), (10, 414), (6, 8)]
    (codeMat 271) (codeMat 458) (codeMat 458) false
    det271 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1340_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1340_orbit
  simpa only [lower14] using h

theorem space1341_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 20), (129, 29), (66, 30), (33, 276), (19, 373), (10, 414), (6, 8)]
    (codeMat 397) (codeMat 458) (codeMat 458) false
    det397 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1341_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1341_orbit
  simpa only [lower14] using h

theorem space1342_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 386), (130, 384), (66, 387), (33, 97), (19, 373), (10, 235), (6, 130)]
    (codeMat 348) (codeMat 465) (codeMat 465) false
    det348 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1342_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1342_orbit
  simpa only [lower14] using h

theorem space1343_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 139), (129, 413), (64, 360), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 407) (codeMat 87) (codeMat 468) false
    det407 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1343_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1343_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
