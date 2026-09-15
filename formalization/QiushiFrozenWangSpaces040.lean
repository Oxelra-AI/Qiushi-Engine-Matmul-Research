import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1280_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 385), (130, 384), (64, 3), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 340) (codeMat 445) (codeMat 478) false
    det340 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1280_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1280_orbit
  simpa only [lower14] using h

theorem space1281_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 259), (128, 384), (65, 3), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 277) (codeMat 445) (codeMat 478) false
    det277 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1281_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1281_orbit
  simpa only [lower14] using h

theorem space1282_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 23), (131, 29), (65, 3), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 461) (codeMat 431) (codeMat 477) false
    det461 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1282_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1282_orbit
  simpa only [lower14] using h

theorem space1283_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 10), (129, 29), (66, 30), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 397) (codeMat 234) (codeMat 461) false
    det397 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1283_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1283_orbit
  simpa only [lower14] using h

theorem space1284_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (130, 384), (66, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 348) (codeMat 213) (codeMat 470) false
    det348 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1284_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1284_orbit
  simpa only [lower14] using h

theorem space1285_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 131), (128, 384), (67, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 285) (codeMat 213) (codeMat 470) false
    det285 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1285_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1285_orbit
  simpa only [lower14] using h

theorem space1286_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 29), (67, 30), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 460) (codeMat 234) (codeMat 461) false
    det460 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1286_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1286_orbit
  simpa only [lower14] using h

theorem space1287_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 131), (129, 387), (65, 3), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 285) (codeMat 143) (codeMat 482) false
    det285 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1287_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1287_orbit
  simpa only [lower14] using h

theorem space1288_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (129, 30), (64, 3), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 460) (codeMat 185) (codeMat 481) false
    det460 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1288_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1288_orbit
  simpa only [lower14] using h

theorem space1289_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 360), (67, 413), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 415) (codeMat 143) (codeMat 482) false
    det415 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1289_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1289_orbit
  simpa only [lower14] using h

theorem space1290_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 136), (130, 384), (66, 232), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 334) (codeMat 185) (codeMat 481) false
    det334 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1290_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1290_orbit
  simpa only [lower14] using h

theorem space1291_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 131), (128, 384), (65, 3), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 277) (codeMat 157) (codeMat 486) false
    det277 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1291_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1291_orbit
  simpa only [lower14] using h

theorem space1292_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 502), (129, 374), (64, 384), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 279) (codeMat 94) (codeMat 500) false
    det279 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1292_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1292_orbit
  simpa only [lower14] using h

theorem space1293_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 488), (130, 360), (64, 384), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 271) (codeMat 494) (codeMat 501) false
    det271 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1293_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1293_orbit
  simpa only [lower14] using h

theorem space1294_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 259), (128, 384), (67, 387), (32, 511), (19, 373), (10, 235), (5, 130)]
    (codeMat 285) (codeMat 501) (codeMat 494) false
    det285 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1294_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1294_orbit
  simpa only [lower14] using h

theorem space1295_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (131, 374), (67, 246), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 286) (codeMat 115) (codeMat 492) false
    det286 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1295_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1295_orbit
  simpa only [lower14] using h

theorem space1296_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (130, 360), (66, 232), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 270) (codeMat 171) (codeMat 485) false
    det270 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1296_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1296_orbit
  simpa only [lower14] using h

theorem space1297_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (131, 387), (64, 384), (35, 227), (19, 235), (10, 373), (5, 130)]
    (codeMat 277) (codeMat 458) (codeMat 458) false
    det277 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1297_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1297_orbit
  simpa only [lower14] using h

theorem space1298_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 264), (130, 384), (64, 360), (35, 284), (19, 414), (10, 373), (5, 8)]
    (codeMat 335) (codeMat 465) (codeMat 465) false
    det335 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1298_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1298_orbit
  simpa only [lower14] using h

theorem space1299_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 28), (131, 30), (67, 29), (35, 284), (19, 414), (10, 373), (5, 8)]
    (codeMat 396) (codeMat 465) (codeMat 465) false
    det396 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1299_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1299_orbit
  simpa only [lower14] using h

theorem space1300_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 353), (130, 360), (67, 245), (35, 227), (19, 235), (10, 373), (5, 130)]
    (codeMat 470) (codeMat 458) (codeMat 458) false
    det470 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1300_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1300_orbit
  simpa only [lower14] using h

theorem space1301_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (129, 387), (65, 384), (33, 406), (19, 235), (10, 373), (4, 130)]
    (codeMat 340) (codeMat 234) (codeMat 461) false
    det340 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1301_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1301_orbit
  simpa only [lower14] using h

theorem space1302_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (128, 384), (65, 360), (33, 105), (19, 414), (10, 373), (4, 8)]
    (codeMat 270) (codeMat 213) (codeMat 470) false
    det270 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1302_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1302_orbit
  simpa only [lower14] using h

theorem space1303_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 362), (131, 363), (64, 3), (33, 284), (19, 235), (10, 373), (4, 511)]
    (codeMat 412) (codeMat 445) (codeMat 478) false
    det412 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1303_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1303_orbit
  simpa only [lower14] using h

theorem space1304_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 362), (130, 360), (64, 3), (33, 227), (19, 414), (10, 373), (4, 511)]
    (codeMat 468) (codeMat 431) (codeMat 477) false
    det468 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1304_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1304_orbit
  simpa only [lower14] using h

theorem space1305_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (131, 30), (67, 29), (33, 105), (19, 414), (10, 373), (4, 8)]
    (codeMat 396) (codeMat 213) (codeMat 470) false
    det396 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1305_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1305_orbit
  simpa only [lower14] using h

theorem space1306_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 404), (130, 360), (67, 245), (33, 406), (19, 235), (10, 373), (4, 130)]
    (codeMat 470) (codeMat 234) (codeMat 461) false
    det470 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1306_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1306_orbit
  simpa only [lower14] using h

theorem space1307_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 393), (129, 246), (66, 374), (33, 227), (19, 414), (10, 373), (4, 511)]
    (codeMat 342) (codeMat 431) (codeMat 477) false
    det342 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1307_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1307_orbit
  simpa only [lower14] using h

theorem space1308_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 118), (128, 384), (66, 374), (33, 284), (19, 235), (10, 373), (4, 511)]
    (codeMat 286) (codeMat 445) (codeMat 478) false
    det286 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1308_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1308_orbit
  simpa only [lower14] using h

theorem space1309_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 30), (65, 3), (35, 97), (19, 414), (10, 235), (4, 8)]
    (codeMat 397) (codeMat 157) (codeMat 486) false
    det397 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1309_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1309_orbit
  simpa only [lower14] using h

theorem space1310_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 278), (129, 413), (64, 360), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 407) (codeMat 115) (codeMat 492) false
    det407 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1310_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1310_orbit
  simpa only [lower14] using h

theorem space1311_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 149), (131, 363), (64, 360), (35, 227), (19, 235), (10, 414), (4, 511)]
    (codeMat 405) (codeMat 501) (codeMat 494) false
    det405 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1311_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1311_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
