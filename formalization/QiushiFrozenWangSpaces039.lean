import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1248_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 383), (130, 384), (67, 246), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 342) (codeMat 241) (codeMat 489) false
    det342 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1248_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1248_orbit
  simpa only [lower14] using h

theorem space1249_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (130, 3), (64, 384), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 285) (codeMat 346) (codeMat 459) false
    det285 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1249_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1249_orbit
  simpa only [lower14] using h

theorem space1250_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 264), (131, 232), (64, 360), (35, 276), (19, 235), (10, 373), (5, 8)]
    (codeMat 334) (codeMat 339) (codeMat 467) false
    det334 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1250_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1250_orbit
  simpa only [lower14] using h

theorem space1251_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 150), (128, 360), (65, 3), (35, 406), (19, 414), (10, 373), (5, 511)]
    (codeMat 405) (codeMat 395) (codeMat 474) false
    det405 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1251_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1251_orbit
  simpa only [lower14] using h

theorem space1252_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 150), (129, 363), (65, 3), (35, 105), (19, 235), (10, 373), (5, 511)]
    (codeMat 477) (codeMat 409) (codeMat 473) false
    det477 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1252_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1252_orbit
  simpa only [lower14] using h

theorem space1253_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (66, 374), (35, 105), (19, 235), (10, 373), (5, 511)]
    (codeMat 286) (codeMat 409) (codeMat 473) false
    det286 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1253_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1253_orbit
  simpa only [lower14] using h

theorem space1254_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 255), (129, 246), (66, 374), (35, 406), (19, 414), (10, 373), (5, 511)]
    (codeMat 342) (codeMat 395) (codeMat 474) false
    det342 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1254_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1254_orbit
  simpa only [lower14] using h

theorem space1255_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 20), (130, 3), (67, 29), (35, 276), (19, 235), (10, 373), (5, 8)]
    (codeMat 397) (codeMat 339) (codeMat 467) false
    det397 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1255_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1255_orbit
  simpa only [lower14] using h

theorem space1256_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 483), (131, 413), (67, 245), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 478) (codeMat 346) (codeMat 459) false
    det478 det346 inv346
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1256_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1256_orbit
  simpa only [lower14] using h

theorem space1257_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 136), (129, 232), (65, 384), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 335) (codeMat 122) (codeMat 460) false
    det335 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1257_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1257_orbit
  simpa only [lower14] using h

theorem space1258_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 413), (65, 360), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 470) (codeMat 87) (codeMat 468) false
    det470 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1258_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1258_orbit
  simpa only [lower14] using h

theorem space1259_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (66, 30), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 396) (codeMat 122) (codeMat 460) false
    det396 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1259_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1259_orbit
  simpa only [lower14] using h

theorem space1260_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 131), (130, 3), (66, 387), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 277) (codeMat 87) (codeMat 468) false
    det277 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1260_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1260_orbit
  simpa only [lower14] using h

theorem space1261_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 264), (128, 360), (65, 384), (33, 276), (19, 373), (10, 414), (6, 8)]
    (codeMat 334) (codeMat 458) (codeMat 458) false
    det334 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1261_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1261_orbit
  simpa only [lower14] using h

theorem space1262_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 353), (131, 245), (65, 360), (33, 97), (19, 373), (10, 235), (6, 130)]
    (codeMat 415) (codeMat 465) (codeMat 465) false
    det415 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1262_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1262_orbit
  simpa only [lower14] using h

theorem space1263_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (67, 387), (33, 97), (19, 373), (10, 235), (6, 130)]
    (codeMat 285) (codeMat 465) (codeMat 465) false
    det285 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1263_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1263_orbit
  simpa only [lower14] using h

theorem space1264_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 28), (131, 29), (67, 30), (33, 276), (19, 373), (10, 414), (6, 8)]
    (codeMat 460) (codeMat 458) (codeMat 458) false
    det460 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1264_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1264_orbit
  simpa only [lower14] using h

theorem space1265_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 131), (130, 3), (64, 384), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 285) (codeMat 94) (codeMat 500) false
    det285 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1265_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1265_orbit
  simpa only [lower14] using h

theorem space1266_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 259), (131, 387), (64, 384), (34, 381), (19, 235), (10, 373), (6, 130)]
    (codeMat 277) (codeMat 494) (codeMat 501) false
    det277 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1266_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1266_orbit
  simpa only [lower14] using h

theorem space1267_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 488), (128, 384), (65, 360), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 270) (codeMat 501) (codeMat 494) false
    det270 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1267_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1267_orbit
  simpa only [lower14] using h

theorem space1268_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (129, 232), (65, 360), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 271) (codeMat 115) (codeMat 492) false
    det271 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1268_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1268_orbit
  simpa only [lower14] using h

theorem space1269_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 502), (128, 384), (66, 374), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 286) (codeMat 157) (codeMat 486) false
    det286 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1269_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1269_orbit
  simpa only [lower14] using h

theorem space1270_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (131, 246), (67, 374), (34, 381), (19, 414), (10, 373), (6, 511)]
    (codeMat 279) (codeMat 171) (codeMat 485) false
    det279 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1270_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1270_orbit
  simpa only [lower14] using h

theorem space1271_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 363), (64, 3), (32, 130), (19, 235), (10, 373), (7, 511)]
    (codeMat 412) (codeMat 185) (codeMat 481) false
    det412 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1271_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1271_orbit
  simpa only [lower14] using h

theorem space1272_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 509), (129, 363), (65, 3), (32, 130), (19, 235), (10, 373), (7, 511)]
    (codeMat 477) (codeMat 185) (codeMat 481) false
    det477 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1272_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1272_orbit
  simpa only [lower14] using h

theorem space1273_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 246), (66, 374), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 342) (codeMat 143) (codeMat 482) false
    det342 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1273_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1273_orbit
  simpa only [lower14] using h

theorem space1274_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 502), (131, 246), (67, 374), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 279) (codeMat 143) (codeMat 482) false
    det279 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1274_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1274_orbit
  simpa only [lower14] using h

theorem space1275_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (129, 246), (64, 384), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 286) (codeMat 458) (codeMat 458) false
    det286 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1275_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1275_orbit
  simpa only [lower14] using h

theorem space1276_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 150), (131, 363), (64, 360), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 405) (codeMat 465) (codeMat 465) false
    det405 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1276_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1276_orbit
  simpa only [lower14] using h

theorem space1277_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 361), (129, 363), (65, 360), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 468) (codeMat 465) (codeMat 465) false
    det468 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1277_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1277_orbit
  simpa only [lower14] using h

theorem space1278_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 255), (131, 246), (65, 384), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 351) (codeMat 458) (codeMat 458) false
    det351 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1278_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1278_orbit
  simpa only [lower14] using h

theorem space1279_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 31), (129, 29), (64, 3), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 396) (codeMat 431) (codeMat 477) false
    det396 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1279_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1279_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
