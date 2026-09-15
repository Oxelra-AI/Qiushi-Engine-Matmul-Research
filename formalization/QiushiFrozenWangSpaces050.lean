import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1600_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [292, 128, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(292, 4), (128, 219), (66, 82), (18, 216), (10, 208), (1, 128)]
    (codeMat 87) (codeMat 282) (codeMat 267) false
    det87 det282 inv282
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1600_lower : 12 ≤ frozenWangTable.L0 (spanCodes [292, 128, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1600_orbit
  simpa only [lower23] using h

theorem space1601_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [262, 128, 70, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(262, 327), (128, 2), (70, 324), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 92) (codeMat 372) (codeMat 93) false
    det92 det372 inv372
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1601_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 128, 70, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1601_orbit
  simpa only [lower10] using h

theorem space1602_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 128, 68, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (128, 2), (68, 324), (38, 168), (18, 16), (10, 416), (1, 256)]
    (codeMat 92) (codeMat 340) (codeMat 85) false
    det92 det340 inv340
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1602_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1602_orbit
  simpa only [lower10] using h

theorem space1603_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 130, 68, 36, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (130, 2), (68, 324), (36, 8), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 84) (codeMat 84) false
    det93 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1603_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 68, 36, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1603_orbit
  simpa only [lower10] using h

theorem space1604_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 132, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 235), (132, 414), (70, 227), (34, 363), (18, 360), (10, 362), (1, 511)]
    (codeMat 482) (codeMat 491) (codeMat 375) false
    det482 det491 inv491
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1604_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 132, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1604_orbit
  simpa only [lower14] using h

theorem space1605_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 134, 68, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 105), (134, 97), (68, 284), (34, 361), (18, 360), (10, 362), (1, 511)]
    (codeMat 482) (codeMat 459) (codeMat 346) false
    det482 det459 inv459
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1605_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 68, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1605_orbit
  simpa only [lower14] using h

theorem space1606_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 68, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 326), (68, 324), (34, 424), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 468) (codeMat 87) false
    det84 det468 inv468
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1606_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1606_orbit
  simpa only [lower10] using h

theorem space1607_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 70, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (132, 326), (70, 68), (32, 24), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 244) (codeMat 95) false
    det85 det244 inv244
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1607_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 70, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1607_orbit
  simpa only [lower10] using h

theorem space1608_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 134, 68, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (134, 70), (68, 324), (32, 8), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 212) (codeMat 86) false
    det85 det212 inv212
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1608_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 134, 68, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1608_orbit
  simpa only [lower10] using h

theorem space1609_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 162, 66, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (162, 246), (66, 178), (18, 432), (10, 176), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 412) (codeMat 111) false
    det142 det412 inv412
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1609_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 162, 66, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1609_orbit
  simpa only [lower10] using h

theorem space1610_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 160, 66, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 503), (160, 70), (66, 178), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 444) (codeMat 110) false
    det142 det444 inv444
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1610_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 160, 66, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1610_orbit
  simpa only [lower10] using h

theorem space1611_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [386, 64, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(386, 71), (64, 128), (34, 55), (18, 63), (10, 23), (6, 1), (1, 2)]
    (codeMat 273) (codeMat 442) (codeMat 334) false
    det273 det442 inv442
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1611_lower : 12 ≤ frozenWangTable.L0 (spanCodes [386, 64, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1611_orbit
  simpa only [lower11] using h

theorem space1612_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [448, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(448, 4), (32, 8), (18, 216), (10, 209), (6, 128), (1, 130)]
    (codeMat 266) (codeMat 241) (codeMat 489) true
    det266 det241 inv241
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1612_lower : 12 ≤ frozenWangTable.L0 (spanCodes [448, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1612_orbit
  simpa only [lower23] using h

theorem space1613_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 160, 98, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 130), (160, 381), (98, 116), (18, 360), (10, 352), (4, 128), (1, 256)]
    (codeMat 87) (codeMat 226) (codeMat 141) false
    det87 det226 inv226
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1613_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 98, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1613_orbit
  simpa only [lower14] using h

theorem space1614_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 162, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 29), (162, 246), (66, 21), (18, 360), (10, 151), (4, 3), (1, 2)]
    (codeMat 481) (codeMat 174) (codeMat 359) false
    det481 det174 inv174
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1614_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 162, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1614_orbit
  simpa only [lower14] using h

theorem space1615_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 162, 64, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (162, 246), (64, 2), (18, 432), (10, 176), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 188) (codeMat 103) false
    det140 det188 inv188
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1615_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 162, 64, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1615_orbit
  simpa only [lower10] using h

theorem space1616_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 192, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 112), (192, 128), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    det266 det212 inv212
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1616_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 192, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1616_orbit
  simpa only [lower11] using h

theorem space1617_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 452), (130, 455), (64, 2), (32, 32), (18, 504), (10, 464), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 410) (codeMat 331) false
    det84 det410 inv410
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1617_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1617_orbit
  simpa only [lower3] using h

theorem space1618_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 66, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 196), (128, 3), (66, 198), (32, 32), (18, 216), (10, 240), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 346) (codeMat 459) false
    det84 det346 inv346
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1618_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1618_orbit
  simpa only [lower3] using h

theorem space1619_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 198), (128, 3), (64, 2), (34, 240), (18, 216), (10, 208), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 314) (codeMat 271) false
    det84 det314 inv314
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1619_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1619_orbit
  simpa only [lower3] using h

theorem space1620_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 66, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (128, 3), (66, 198), (34, 208), (18, 216), (10, 240), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 122) (codeMat 460) false
    det84 det122 inv122
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1620_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1620_orbit
  simpa only [lower3] using h

theorem space1621_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    det84 det286 inv286
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1621_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1621_orbit
  simpa only [lower3] using h

theorem space1622_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 130, 64, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (130, 455), (64, 2), (32, 8), (18, 504), (10, 464), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 158) (codeMat 358) false
    det84 det158 inv158
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1622_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1622_orbit
  simpa only [lower3] using h

theorem space1623_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    det84 det94 inv94
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1623_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1623_orbit
  simpa only [lower3] using h

theorem space1624_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 66, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 453), (130, 455), (66, 454), (32, 40), (18, 504), (10, 496), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 478) (codeMat 445) false
    det84 det478 inv478
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1624_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1624_orbit
  simpa only [lower3] using h

theorem space1625_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 199), (128, 3), (66, 198), (34, 248), (18, 216), (10, 240), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    det84 det382 inv382
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1625_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1625_orbit
  simpa only [lower3] using h

theorem space1626_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (130, 455), (66, 454), (34, 472), (18, 504), (10, 496), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 254) (codeMat 443) false
    det84 det254 inv254
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1626_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1626_orbit
  simpa only [lower3] using h

theorem space1627_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 68), (129, 70), (64, 1), (32, 32), (17, 112), (8, 8), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 401) (codeMat 401) false
    det84 det401 inv401
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1627_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1627_orbit
  simpa only [lower3] using h

theorem space1628_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 324), (128, 2), (65, 325), (32, 32), (17, 336), (8, 40), (4, 256), (2, 128)]
    (codeMat 84) (codeMat 337) (codeMat 337) false
    det84 det337 inv337
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1628_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1628_orbit
  simpa only [lower3] using h

theorem space1629_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 70), (128, 2), (64, 1), (33, 112), (17, 80), (8, 8), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 305) (codeMat 305) false
    det84 det305 inv305
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1629_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1629_orbit
  simpa only [lower3] using h

theorem space1630_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 70), (64, 1), (33, 80), (17, 112), (8, 8), (4, 128), (2, 384)]
    (codeMat 84) (codeMat 177) (codeMat 417) false
    det84 det177 inv177
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1630_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1630_orbit
  simpa only [lower3] using h

theorem space1631_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 69), (128, 2), (64, 1), (32, 40), (17, 80), (8, 8), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 277) (codeMat 277) false
    det84 det277 inv277
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1631_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1631_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
