import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1376_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 488), (128, 384), (67, 232), (32, 511), (19, 414), (10, 235), (6, 8)]
    (codeMat 271) (codeMat 445) (codeMat 478) false
    det271 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1376_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1376_orbit
  simpa only [lower14] using h

theorem space1377_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 385), (131, 387), (64, 3), (32, 511), (19, 235), (10, 414), (6, 130)]
    (codeMat 348) (codeMat 431) (codeMat 477) false
    det348 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1377_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1377_orbit
  simpa only [lower14] using h

theorem space1378_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 31), (129, 30), (64, 3), (32, 511), (19, 414), (10, 235), (6, 8)]
    (codeMat 460) (codeMat 445) (codeMat 478) false
    det460 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1378_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1378_orbit
  simpa only [lower14] using h

theorem space1379_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 383), (131, 246), (65, 384), (32, 130), (19, 414), (10, 235), (6, 511)]
    (codeMat 351) (codeMat 234) (codeMat 461) false
    det351 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1379_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1379_orbit
  simpa only [lower14] using h

theorem space1380_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (129, 363), (65, 360), (32, 8), (19, 235), (10, 414), (6, 511)]
    (codeMat 468) (codeMat 213) (codeMat 470) false
    det468 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1380_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1380_orbit
  simpa only [lower14] using h

theorem space1381_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 150), (130, 3), (66, 363), (33, 406), (19, 373), (10, 235), (6, 511)]
    (codeMat 405) (codeMat 346) (codeMat 459) false
    det405 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1381_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1381_orbit
  simpa only [lower14] using h

theorem space1382_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 255), (129, 374), (66, 246), (33, 105), (19, 373), (10, 414), (6, 511)]
    (codeMat 351) (codeMat 339) (codeMat 467) false
    det351 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1382_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1382_orbit
  simpa only [lower14] using h

theorem space1383_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 483), (131, 245), (67, 413), (33, 227), (19, 373), (10, 414), (6, 130)]
    (codeMat 407) (codeMat 409) (codeMat 473) false
    det407 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1383_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1383_orbit
  simpa only [lower14] using h

theorem space1384_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 264), (128, 360), (67, 232), (33, 284), (19, 373), (10, 235), (6, 8)]
    (codeMat 335) (codeMat 395) (codeMat 474) false
    det335 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1384_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1384_orbit
  simpa only [lower14] using h

theorem space1385_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 150), (130, 3), (64, 360), (33, 105), (19, 373), (10, 414), (6, 511)]
    (codeMat 477) (codeMat 339) (codeMat 467) false
    det477 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1385_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1385_orbit
  simpa only [lower14] using h

theorem space1386_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (129, 374), (64, 384), (33, 406), (19, 373), (10, 235), (6, 511)]
    (codeMat 279) (codeMat 346) (codeMat 459) false
    det279 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1386_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1386_orbit
  simpa only [lower14] using h

theorem space1387_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 20), (131, 29), (65, 3), (33, 284), (19, 373), (10, 235), (6, 8)]
    (codeMat 461) (codeMat 395) (codeMat 474) false
    det461 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1387_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1387_orbit
  simpa only [lower14] using h

theorem space1388_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (65, 3), (33, 227), (19, 373), (10, 414), (6, 130)]
    (codeMat 277) (codeMat 409) (codeMat 473) false
    det277 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1388_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1388_orbit
  simpa only [lower14] using h

theorem space1389_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 264), (130, 384), (66, 232), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 334) (codeMat 409) (codeMat 473) false
    det334 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1389_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1389_orbit
  simpa only [lower14] using h

theorem space1390_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 483), (128, 360), (66, 413), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 478) (codeMat 395) (codeMat 474) false
    det478 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1390_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1390_orbit
  simpa only [lower14] using h

theorem space1391_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 353), (130, 360), (67, 413), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 415) (codeMat 395) (codeMat 474) false
    det415 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1391_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1391_orbit
  simpa only [lower14] using h

theorem space1392_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (67, 232), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 271) (codeMat 409) (codeMat 473) false
    det271 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1392_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1392_orbit
  simpa only [lower14] using h

theorem space1393_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (131, 232), (64, 384), (34, 284), (19, 235), (10, 414), (7, 8)]
    (codeMat 270) (codeMat 346) (codeMat 459) false
    det270 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1393_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1393_orbit
  simpa only [lower14] using h

theorem space1394_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 483), (129, 413), (64, 360), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 407) (codeMat 339) (codeMat 467) false
    det407 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1394_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1394_orbit
  simpa only [lower14] using h

theorem space1395_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 353), (131, 413), (65, 360), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 470) (codeMat 339) (codeMat 467) false
    det470 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1395_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1395_orbit
  simpa only [lower14] using h

theorem space1396_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 264), (129, 232), (65, 384), (34, 284), (19, 235), (10, 414), (7, 8)]
    (codeMat 335) (codeMat 346) (codeMat 459) false
    det335 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1396_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1396_orbit
  simpa only [lower14] using h

theorem space1397_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 488), (130, 360), (66, 232), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 270) (codeMat 431) (codeMat 477) false
    det270 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1397_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1397_orbit
  simpa only [lower14] using h

theorem space1398_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 252), (129, 245), (66, 413), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 470) (codeMat 445) (codeMat 478) false
    det470 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1398_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1398_orbit
  simpa only [lower14] using h

theorem space1399_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 126), (131, 245), (67, 413), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 407) (codeMat 445) (codeMat 478) false
    det407 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1399_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1399_orbit
  simpa only [lower14] using h

theorem space1400_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 480), (128, 360), (67, 232), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 335) (codeMat 431) (codeMat 477) false
    det335 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1400_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1400_orbit
  simpa only [lower14] using h

theorem space1401_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (130, 360), (64, 384), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 271) (codeMat 234) (codeMat 461) false
    det271 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1401_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1401_orbit
  simpa only [lower14] using h

theorem space1402_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 139), (129, 245), (64, 360), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 478) (codeMat 213) (codeMat 470) false
    det478 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1402_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1402_orbit
  simpa only [lower14] using h

theorem space1403_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 245), (65, 360), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 415) (codeMat 213) (codeMat 470) false
    det415 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1403_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1403_orbit
  simpa only [lower14] using h

theorem space1404_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 136), (128, 360), (65, 384), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 334) (codeMat 234) (codeMat 461) false
    det334 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1404_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1404_orbit
  simpa only [lower14] using h

theorem space1405_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 139), (128, 360), (66, 245), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 407) (codeMat 206) (codeMat 498) false
    det407 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1405_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1405_orbit
  simpa only [lower14] using h

theorem space1406_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 252), (129, 413), (66, 245), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 415) (codeMat 382) (codeMat 499) false
    det415 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1406_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1406_orbit
  simpa only [lower14] using h

theorem space1407_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 360), (67, 245), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 470) (codeMat 206) (codeMat 498) false
    det470 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1407_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1407_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
