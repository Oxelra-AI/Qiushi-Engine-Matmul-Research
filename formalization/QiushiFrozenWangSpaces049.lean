import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1568_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 69, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (128, 128), (69, 392), (33, 510), (16, 2), (9, 511), (3, 360)]
    (codeMat 298) (codeMat 377) (codeMat 369) false
    det298 det377 inv377
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1568_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 69, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1568_orbit
  simpa only [lower14] using h

theorem space1569_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 129, 65, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 198), (129, 129), (65, 3), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 85) (codeMat 299) (codeMat 318) false
    det85 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1569_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1569_orbit
  simpa only [lower11] using h

theorem space1570_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 129, 64, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (129, 137), (64, 219), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 299) (codeMat 318) false
    det87 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1570_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 64, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1570_orbit
  simpa only [lower11] using h

theorem space1571_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 68, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 2), (68, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    det84 det92 inv92
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1571_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1571_orbit
  simpa only [lower10] using h

theorem space1572_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 129, 64, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 228), (129, 137), (64, 219), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 267) (codeMat 282) false
    det87 det267 inv267
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1572_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 64, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1572_orbit
  simpa only [lower11] using h

theorem space1573_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [289, 161, 97, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(289, 503), (161, 500), (97, 502), (16, 256), (9, 432), (5, 8), (3, 16)]
    (codeMat 140) (codeMat 492) (codeMat 115) false
    det140 det492 inv492
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1573_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 161, 97, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1573_orbit
  simpa only [lower10] using h

theorem space1574_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 65, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (160, 149), (65, 9), (16, 360), (9, 8), (5, 384), (3, 256)]
    (codeMat 94) (codeMat 423) (codeMat 181) false
    det94 det423 inv423
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1574_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 65, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1574_orbit
  simpa only [lower14] using h

theorem space1575_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [288, 129, 64, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(288, 54), (129, 138), (64, 219), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 143) (codeMat 313) (codeMat 313) false
    det143 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1575_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 64, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1575_orbit
  simpa only [lower11] using h

theorem space1576_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 64, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 80), (64, 128), (32, 54), (16, 63), (9, 2), (5, 32), (3, 40)]
    (codeMat 267) (codeMat 442) (codeMat 334) false
    det267 det442 inv442
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1576_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 64, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1576_orbit
  simpa only [lower11] using h

theorem space1577_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 128, 65, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 28), (128, 130), (65, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 142) (codeMat 281) (codeMat 281) false
    det142 det281 inv281
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1577_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 128, 65, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1577_orbit
  simpa only [lower11] using h

theorem space1578_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 64, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (160, 149), (64, 1), (16, 360), (9, 8), (4, 128), (3, 256)]
    (codeMat 92) (codeMat 163) (codeMat 165) false
    det92 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1578_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1578_orbit
  simpa only [lower14] using h

theorem space1579_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [320, 129, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(320, 128), (129, 240), (33, 52), (16, 3), (9, 54), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 346) (codeMat 459) false
    det266 det346 inv346
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1579_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 129, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1579_orbit
  simpa only [lower11] using h

theorem space1580_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 133, 68, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 71), (133, 324), (68, 70), (37, 440), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 492) (codeMat 115) false
    det93 det492 inv492
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1580_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 68, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1580_orbit
  simpa only [lower10] using h

theorem space1581_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 65, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (129, 210), (65, 219), (37, 240), (17, 80), (8, 216), (2, 128)]
    (codeMat 95) (codeMat 313) (codeMat 313) false
    det95 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1581_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1581_orbit
  simpa only [lower11] using h

theorem space1582_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 69, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 8), (132, 96), (69, 392), (36, 1), (17, 149), (8, 511), (2, 360)]
    (codeMat 355) (codeMat 207) (codeMat 370) false
    det355 det207 inv207
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1582_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 69, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1582_orbit
  simpa only [lower14] using h

theorem space1583_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 68, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 130), (129, 97), (68, 381), (36, 128), (17, 96), (8, 360), (2, 8)]
    (codeMat 206) (codeMat 99) (codeMat 172) false
    det206 det99 inv99
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1583_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1583_orbit
  simpa only [lower14] using h

theorem space1584_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 65, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (132, 509), (65, 1), (36, 128), (17, 96), (8, 8), (2, 360)]
    (codeMat 213) (codeMat 163) (codeMat 165) false
    det213 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1584_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1584_orbit
  simpa only [lower14] using h

theorem space1585_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 68, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 227), (129, 97), (68, 284), (33, 224), (17, 96), (8, 256), (2, 8)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    det142 det102 inv102
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1585_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1585_orbit
  simpa only [lower14] using h

theorem space1586_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 276), (133, 227), (64, 130), (33, 148), (17, 149), (8, 2), (2, 511)]
    (codeMat 426) (codeMat 442) (codeMat 334) false
    det426 det442 inv442
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1586_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1586_orbit
  simpa only [lower14] using h

theorem space1587_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 69, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (132, 509), (69, 148), (32, 128), (17, 96), (8, 256), (2, 360)]
    (codeMat 157) (codeMat 226) (codeMat 141) false
    det157 det226 inv226
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1587_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1587_orbit
  simpa only [lower14] using h

theorem space1588_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 65, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 136), (133, 96), (65, 128), (32, 3), (17, 149), (8, 2), (2, 360)]
    (codeMat 354) (codeMat 174) (codeMat 359) false
    det354 det174 inv174
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1588_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1588_orbit
  simpa only [lower14] using h

theorem space1589_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 129, 65, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 100), (129, 210), (65, 9), (32, 32), (17, 80), (8, 8), (2, 128)]
    (codeMat 87) (codeMat 273) (codeMat 273) false
    det87 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1589_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1589_orbit
  simpa only [lower11] using h

theorem space1590_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 64, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (133, 68), (64, 2), (32, 24), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    det84 det172 inv172
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1590_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1590_orbit
  simpa only [lower10] using h

theorem space1591_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 160, 96, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 511), (160, 508), (96, 509), (17, 96), (8, 360), (5, 128), (2, 256)]
    (codeMat 92) (codeMat 485) (codeMat 171) false
    det92 det485 inv485
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1591_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 96, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1591_orbit
  simpa only [lower14] using h

theorem space1592_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [288, 129, 65, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(288, 54), (129, 89), (65, 130), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 143) (codeMat 298) (codeMat 270) false
    det143 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1592_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 65, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1592_orbit
  simpa only [lower11] using h

theorem space1593_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 193, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (193, 248), (33, 42), (17, 28), (8, 63), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 233) (codeMat 233) false
    det267 det233 inv233
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1593_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 193, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1593_orbit
  simpa only [lower11] using h

theorem space1594_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 128, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 197), (128, 128), (33, 53), (17, 21), (8, 40), (5, 3), (2, 2)]
    (codeMat 273) (codeMat 369) (codeMat 377) false
    det273 det369 inv369
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1594_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 128, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1594_orbit
  simpa only [lower11] using h

theorem space1595_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [384, 65, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(384, 128), (65, 216), (33, 30), (17, 28), (8, 3), (5, 40), (2, 32)]
    (codeMat 266) (codeMat 425) (codeMat 249) false
    det266 det425 inv425
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1595_lower : 12 ≤ frozenWangTable.L0 (spanCodes [384, 65, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1595_orbit
  simpa only [lower11] using h

theorem space1596_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 64, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 208), (64, 128), (33, 22), (17, 21), (8, 2), (5, 32), (2, 40)]
    (codeMat 266) (codeMat 426) (codeMat 335) false
    det266 det426 inv426
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1596_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 64, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1596_orbit
  simpa only [lower11] using h

theorem space1597_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 97, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (128, 2), (97, 228), (17, 160), (8, 256), (4, 24), (2, 16)]
    (codeMat 140) (codeMat 116) (codeMat 92) false
    det140 det116 inv116
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1597_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 97, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1597_orbit
  simpa only [lower10] using h

theorem space1598_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 129, 65, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 52), (129, 89), (65, 130), (17, 80), (8, 128), (4, 32), (2, 8)]
    (codeMat 143) (codeMat 266) (codeMat 266) false
    det143 det266 inv266
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1598_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 129, 65, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1598_orbit
  simpa only [lower11] using h

theorem space1599_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 65, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 88), (65, 216), (33, 28), (17, 29), (8, 3), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 395) (codeMat 474) false
    det266 det395 inv395
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1599_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 65, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1599_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
