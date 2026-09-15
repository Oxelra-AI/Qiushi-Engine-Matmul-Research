import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1216_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 132, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 71), (132, 70), (70, 324), (34, 440), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 500) (codeMat 94) false
    det85 det500 inv500
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1216_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 132, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1216_orbit
  simpa only [lower10] using h

theorem space1217_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 66, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 228), (130, 219), (66, 210), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    det86 det282 inv282
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1217_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1217_orbit
  simpa only [lower11] using h

theorem space1218_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 134, 64, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (134, 21), (64, 9), (32, 128), (18, 360), (10, 104), (1, 8)]
    (codeMat 141) (codeMat 163) (codeMat 165) false
    det141 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1218_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 134, 64, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1218_orbit
  simpa only [lower14] using h

theorem space1219_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 64, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (132, 28), (64, 1), (38, 224), (18, 256), (10, 104), (1, 8)]
    (codeMat 204) (codeMat 165) (codeMat 163) false
    det204 det165 inv165
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1219_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1219_orbit
  simpa only [lower14] using h

theorem space1220_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 70, 36, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (128, 2), (70, 68), (36, 24), (18, 16), (10, 416), (1, 256)]
    (codeMat 92) (codeMat 116) (codeMat 92) false
    det92 det116 inv116
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1220_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 70, 36, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1220_orbit
  simpa only [lower10] using h

theorem space1221_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (65, 384), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 348) (codeMat 122) (codeMat 460) false
    det348 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1221_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1221_orbit
  simpa only [lower14] using h

theorem space1222_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (129, 232), (65, 360), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 271) (codeMat 87) (codeMat 468) false
    det271 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1222_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1222_orbit
  simpa only [lower14] using h

theorem space1223_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 3), (67, 29), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 397) (codeMat 87) (codeMat 468) false
    det397 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1223_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1223_orbit
  simpa only [lower14] using h

theorem space1224_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 67, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 278), (131, 413), (67, 245), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 478) (codeMat 122) (codeMat 460) false
    det478 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1224_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1224_orbit
  simpa only [lower14] using h

theorem space1225_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (130, 384), (64, 3), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 340) (codeMat 185) (codeMat 481) false
    det340 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1225_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1225_orbit
  simpa only [lower14] using h

theorem space1226_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 29), (65, 3), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 461) (codeMat 143) (codeMat 482) false
    det461 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1226_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1226_orbit
  simpa only [lower14] using h

theorem space1227_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 104), (130, 360), (66, 232), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 270) (codeMat 143) (codeMat 482) false
    det270 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1227_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1227_orbit
  simpa only [lower14] using h

theorem space1228_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 278), (131, 245), (67, 413), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 407) (codeMat 185) (codeMat 481) false
    det407 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1228_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1228_orbit
  simpa only [lower14] using h

theorem space1229_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (131, 387), (64, 3), (35, 276), (19, 235), (10, 414), (4, 130)]
    (codeMat 348) (codeMat 171) (codeMat 485) false
    det348 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1229_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1229_orbit
  simpa only [lower14] using h

theorem space1230_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 96), (129, 232), (65, 384), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 335) (codeMat 94) (codeMat 500) false
    det335 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1230_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1230_orbit
  simpa only [lower14] using h

theorem space1231_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 393), (131, 246), (65, 384), (35, 284), (19, 414), (10, 235), (4, 511)]
    (codeMat 351) (codeMat 494) (codeMat 501) false
    det351 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1231_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1231_orbit
  simpa only [lower14] using h

theorem space1232_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 96), (130, 384), (66, 232), (35, 97), (19, 414), (10, 235), (4, 8)]
    (codeMat 334) (codeMat 157) (codeMat 486) false
    det334 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1232_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1232_orbit
  simpa only [lower14] using h

theorem space1233_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (67, 387), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 340) (codeMat 115) (codeMat 492) false
    det340 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1233_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1233_orbit
  simpa only [lower14] using h

theorem space1234_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 393), (130, 384), (67, 246), (35, 227), (19, 235), (10, 414), (4, 511)]
    (codeMat 342) (codeMat 501) (codeMat 494) false
    det342 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1234_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1234_orbit
  simpa only [lower14] using h

theorem space1235_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (129, 29), (64, 3), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 396) (codeMat 171) (codeMat 485) false
    det396 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1235_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1235_orbit
  simpa only [lower14] using h

theorem space1236_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (65, 360), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 412) (codeMat 115) (codeMat 492) false
    det412 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1236_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1236_orbit
  simpa only [lower14] using h

theorem space1237_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 252), (131, 245), (65, 360), (32, 511), (19, 373), (10, 235), (5, 130)]
    (codeMat 415) (codeMat 501) (codeMat 494) false
    det415 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1237_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1237_orbit
  simpa only [lower14] using h

theorem space1238_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 23), (129, 29), (66, 30), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 397) (codeMat 494) (codeMat 501) false
    det397 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1238_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1238_orbit
  simpa only [lower14] using h

theorem space1239_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 510), (130, 3), (66, 363), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 405) (codeMat 94) (codeMat 500) false
    det405 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1239_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1239_orbit
  simpa only [lower14] using h

theorem space1240_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 139), (131, 245), (67, 413), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 407) (codeMat 157) (codeMat 486) false
    det407 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1240_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1240_orbit
  simpa only [lower14] using h

theorem space1241_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 502), (129, 246), (64, 384), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 286) (codeMat 206) (codeMat 498) false
    det286 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1241_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1241_orbit
  simpa only [lower14] using h

theorem space1242_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 488), (131, 232), (64, 384), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 270) (codeMat 382) (codeMat 499) false
    det270 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1242_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1242_orbit
  simpa only [lower14] using h

theorem space1243_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (129, 363), (65, 360), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 468) (codeMat 241) (codeMat 489) false
    det468 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1243_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1243_orbit
  simpa only [lower14] using h

theorem space1244_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 252), (131, 413), (65, 360), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 470) (codeMat 375) (codeMat 491) false
    det470 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1244_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1244_orbit
  simpa only [lower14] using h

theorem space1245_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 31), (128, 3), (66, 30), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 396) (codeMat 382) (codeMat 499) false
    det396 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1245_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1245_orbit
  simpa only [lower14] using h

theorem space1246_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (130, 360), (66, 363), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 412) (codeMat 206) (codeMat 498) false
    det412 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1246_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1246_orbit
  simpa only [lower14] using h

theorem space1247_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 385), (128, 3), (67, 387), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 340) (codeMat 375) (codeMat 491) false
    det340 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1247_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1247_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
