import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1472_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 96, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 2), (96, 68), (17, 160), (8, 256), (4, 8), (2, 16)]
    (codeMat 140) (codeMat 84) (codeMat 84) false
    det140 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1472_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 96, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1472_orbit
  simpa only [lower10] using h

theorem space1473_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 129, 64, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 20), (129, 81), (64, 130), (17, 80), (8, 128), (4, 32), (2, 8)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    det142 det266 inv266
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1473_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 129, 64, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1473_orbit
  simpa only [lower11] using h

theorem space1474_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 193, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 120), (193, 248), (32, 9), (17, 28), (8, 63), (4, 8), (2, 32)]
    (codeMat 267) (codeMat 205) (codeMat 242) false
    det267 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1474_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 193, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1474_orbit
  simpa only [lower11] using h

theorem space1475_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 64, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 80), (64, 128), (33, 20), (17, 21), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    det266 det394 inv394
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1475_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 64, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1475_orbit
  simpa only [lower11] using h

theorem space1476_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 160, 96, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 387), (160, 252), (96, 245), (17, 96), (8, 360), (5, 384), (2, 256)]
    (codeMat 95) (codeMat 229) (codeMat 187) false
    det95 det229 inv229
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1476_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 160, 96, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1476_orbit
  simpa only [lower14] using h

theorem space1477_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 96, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (129, 162), (96, 68), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 340) (codeMat 85) false
    det142 det340 inv340
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1477_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 96, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1477_orbit
  simpa only [lower10] using h

theorem space1478_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 97, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 487), (129, 162), (97, 228), (17, 160), (8, 256), (5, 24), (2, 16)]
    (codeMat 142) (codeMat 372) (codeMat 93) false
    det142 det372 inv372
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1478_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 97, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1478_orbit
  simpa only [lower10] using h

theorem space1479_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [448, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(448, 4), (33, 90), (17, 82), (8, 9), (5, 130), (2, 128)]
    (codeMat 266) (codeMat 425) (codeMat 249) true
    det266 det425 inv425
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1479_lower : 12 ≤ frozenWangTable.L0 (spanCodes [448, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1479_orbit
  simpa only [lower23] using h

theorem space1480_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [292, 129, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(292, 4), (129, 137), (64, 219), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 267) (codeMat 282) false
    det87 det267 inv267
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1480_lower : 12 ≤ frozenWangTable.L0 (spanCodes [292, 129, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1480_orbit
  simpa only [lower23] using h

theorem space1481_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 65, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (132, 326), (65, 2), (36, 24), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 188) (codeMat 103) false
    det93 det188 inv188
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1481_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1481_orbit
  simpa only [lower10] using h

theorem space1482_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 68, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (132, 29), (68, 28), (37, 224), (16, 360), (9, 256), (3, 8)]
    (codeMat 204) (codeMat 230) (codeMat 159) false
    det204 det230 inv230
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1482_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1482_orbit
  simpa only [lower14] using h

theorem space1483_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 326), (64, 2), (37, 168), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 412) (codeMat 111) false
    det92 det412 inv412
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1483_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1483_orbit
  simpa only [lower10] using h

theorem space1484_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 133, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 327), (133, 326), (64, 2), (37, 184), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 444) (codeMat 110) false
    det92 det444 inv444
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1484_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1484_orbit
  simpa only [lower10] using h

theorem space1485_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 68, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 8), (129, 381), (68, 97), (32, 1), (16, 2), (9, 360), (3, 511)]
    (codeMat 482) (codeMat 85) (codeMat 340) false
    det482 det85 inv85
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1485_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 68, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1485_orbit
  simpa only [lower14] using h

theorem space1486_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 69, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (128, 2), (69, 326), (32, 24), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 124) (codeMat 124) false
    det84 det124 inv124
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1486_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 69, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1486_orbit
  simpa only [lower10] using h

theorem space1487_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 129, 65, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 196), (129, 129), (65, 3), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 85) (codeMat 267) (codeMat 282) false
    det85 det267 inv267
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1487_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1487_orbit
  simpa only [lower11] using h

theorem space1488_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 68, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 71), (129, 258), (68, 70), (33, 440), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 380) (codeMat 117) false
    det85 det380 inv380
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1488_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1488_orbit
  simpa only [lower10] using h

theorem space1489_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 69, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (129, 258), (69, 326), (33, 424), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 348) (codeMat 125) false
    det85 det348 inv348
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1489_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 69, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1489_orbit
  simpa only [lower10] using h

theorem space1490_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 160, 96, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 29), (160, 284), (96, 414), (16, 511), (9, 360), (4, 3), (3, 2)]
    (codeMat 369) (codeMat 247) (codeMat 379) false
    det369 det247 inv247
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1490_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 160, 96, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1490_orbit
  simpa only [lower14] using h

theorem space1491_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 161, 96, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 3), (161, 500), (96, 326), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 142) (codeMat 236) (codeMat 123) false
    det142 det236 inv236
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1491_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 161, 96, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1491_orbit
  simpa only [lower10] using h

theorem space1492_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 160, 97, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 1), (160, 324), (97, 502), (16, 256), (9, 432), (4, 8), (3, 16)]
    (codeMat 142) (codeMat 204) (codeMat 114) false
    det142 det204 inv204
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1492_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 97, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1492_orbit
  simpa only [lower10] using h

theorem space1493_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 97, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 246), (129, 265), (97, 29), (16, 8), (9, 360), (4, 384), (3, 256)]
    (codeMat 87) (codeMat 355) (codeMat 190) false
    det87 det355 inv355
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1493_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 97, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1493_orbit
  simpa only [lower14] using h

theorem space1494_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 192, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (192, 128), (32, 8), (16, 32), (9, 54), (4, 1), (3, 2)]
    (codeMat 273) (codeMat 204) (codeMat 114) false
    det273 det204 inv204
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1494_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 192, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1494_orbit
  simpa only [lower11] using h

theorem space1495_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [448, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(448, 4), (33, 210), (16, 8), (9, 219), (4, 128), (3, 130)]
    (codeMat 266) (codeMat 345) (codeMat 345) true
    det266 det345 inv345
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1495_lower : 12 ≤ frozenWangTable.L0 (spanCodes [448, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1495_orbit
  simpa only [lower23] using h

theorem space1496_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 160, 96, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 325), (160, 324), (96, 326), (16, 256), (9, 432), (5, 24), (3, 16)]
    (codeMat 140) (codeMat 460) (codeMat 122) false
    det140 det460 inv460
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1496_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 96, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1496_orbit
  simpa only [lower10] using h

theorem space1497_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 128, 65, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 30), (128, 130), (65, 219), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 142) (codeMat 313) (codeMat 313) false
    det142 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1497_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 128, 65, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1497_orbit
  simpa only [lower11] using h

theorem space1498_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 128, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 120), (128, 128), (33, 62), (16, 2), (9, 63), (5, 8), (3, 40)]
    (codeMat 266) (codeMat 377) (codeMat 369) false
    det266 det377 inv377
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1498_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 128, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1498_orbit
  simpa only [lower11] using h

theorem space1499_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 502), (131, 374), (67, 246), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 286) (codeMat 87) (codeMat 468) false
    det286 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1499_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1499_orbit
  simpa only [lower14] using h

theorem space1500_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (67, 363), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 468) (codeMat 122) (codeMat 460) false
    det468 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1500_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1500_orbit
  simpa only [lower14] using h

theorem space1501_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 509), (130, 3), (66, 363), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 405) (codeMat 122) (codeMat 460) false
    det405 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1501_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1501_orbit
  simpa only [lower14] using h

theorem space1502_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 374), (66, 246), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 351) (codeMat 87) (codeMat 468) false
    det351 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1502_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1502_orbit
  simpa only [lower14] using h

theorem space1503_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 255), (130, 384), (67, 246), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 342) (codeMat 465) (codeMat 465) false
    det342 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1503_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space1503_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
