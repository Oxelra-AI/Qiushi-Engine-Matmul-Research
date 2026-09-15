import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2592_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [384, 82, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(384, 128), (82, 246), (50, 22), (10, 30), (6, 2), (1, 3)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    det273 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2592_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 82, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2592_orbit
  simpa only [lower35] using h

theorem space2593_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 67, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (130, 8), (67, 97), (37, 252), (23, 28), (10, 227)]
    (codeMat 125) (codeMat 369) (codeMat 377) true
    det125 det369 inv369
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2593_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 67, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2593_orbit
  simpa only [lower35] using h

theorem space2594_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 67, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (131, 105), (67, 97), (33, 252), (23, 255), (10, 227)]
    (codeMat 124) (codeMat 499) (codeMat 382) true
    det124 det499 inv499
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2594_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2594_orbit
  simpa only [lower35] using h

theorem space2595_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 129, 65, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 238), (129, 287), (65, 27), (39, 160), (21, 336), (10, 480)]
    (codeMat 215) (codeMat 443) (codeMat 254) false
    det215 det443 inv443
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2595_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2595_orbit
  simpa only [lower65] using h

theorem space2596_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 128, 65, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 496), (128, 320), (65, 16), (36, 1), (21, 437), (10, 506)]
    (codeMat 299) (codeMat 142) (codeMat 354) false
    det299 det142 inv142
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2596_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 128, 65, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2596_orbit
  simpa only [lower65] using h

theorem space2597_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [260, 162, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(260, 16), (162, 10), (68, 272), (16, 1), (10, 78)]
    (codeMat 298) (codeMat 106) (codeMat 396) false
    det298 det106 inv106
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space2597_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 162, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space2597_orbit
  simpa only [lower149] using h

theorem space2598_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (134, 96), (69, 224), (39, 148), (17, 149), (10, 151)]
    (codeMat 355) (codeMat 459) (codeMat 346) false
    det355 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2598_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2598_orbit
  simpa only [lower35] using h

theorem space2599_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [261, 133, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(261, 68), (133, 71), (69, 69), (39, 160), (17, 184), (10, 168)]
    (codeMat 92) (codeMat 467) (codeMat 339) false
    det92 det467 inv467
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2599_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2599_orbit
  simpa only [lower29] using h

theorem space2600_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 224), (131, 227), (69, 255), (39, 96), (17, 97), (10, 105)]
    (codeMat 123) (codeMat 459) (codeMat 346) true
    det123 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2600_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2600_orbit
  simpa only [lower35] using h

theorem space2601_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 133, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 224), (133, 252), (69, 255), (36, 128), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 473) (codeMat 409) true
    det95 det473 inv473
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2601_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2601_orbit
  simpa only [lower35] using h

theorem space2602_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 133, 69, 33, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 126), (133, 252), (69, 245), (33, 232), (17, 104), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    det159 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2602_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 69, 33, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2602_orbit
  simpa only [lower35] using h

theorem space2603_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 144, 82, 32, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (144, 3), (82, 252), (32, 8), (10, 224), (6, 128)]
    (codeMat 86) (codeMat 86) (codeMat 212) false
    det86 det86 inv86
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2603_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 144, 82, 32, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space2603_orbit
  simpa only [lower35] using h

theorem space2604_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 131, 82, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 20), (131, 246), (82, 29), (33, 96), (10, 232), (6, 128)]
    (codeMat 95) (codeMat 465) (codeMat 465) false
    det95 det465 inv465
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2604_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 131, 82, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space2604_orbit
  simpa only [lower35] using h

theorem space2605_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 162, 66, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 447), (162, 78), (66, 420), (17, 176), (10, 160), (7, 320)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    det95 det500 inv500
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2605_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 162, 66, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2605_orbit
  simpa only [lower65] using h

theorem space2606_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 162, 65, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 261), (162, 238), (65, 260), (17, 176), (10, 160), (4, 320)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    det92 det468 inv468
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2606_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 65, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space2606_orbit
  simpa only [lower65] using h

theorem space2607_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 145, 81, 51, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 254), (145, 255), (81, 252), (51, 136), (10, 224), (5, 128)]
    (codeMat 92) (codeMat 498) (codeMat 206) false
    det92 det498 inv498
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2607_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 51, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2607_orbit
  simpa only [lower35] using h

theorem space2608_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [272, 130, 81, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(272, 453), (130, 1), (81, 11), (33, 180), (10, 20), (5, 432)]
    (codeMat 213) (codeMat 271) (codeMat 314) true
    det213 det271 inv271
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space2608_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 130, 81, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 80 space2608_orbit
  simpa only [lower80] using h

theorem space2609_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 135, 67, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 1), (135, 436), (67, 507), (39, 496), (23, 176), (10, 480)]
    (codeMat 156) (codeMat 141) (codeMat 226) false
    det156 det141 inv141
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2609_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 67, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2609_orbit
  simpa only [lower65] using h

theorem space2610_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 134, 65, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 176), (134, 160), (65, 320), (34, 436), (21, 78), (10, 437)]
    (codeMat 354) (codeMat 465) (codeMat 465) false
    det354 det465 inv465
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2610_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 65, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2610_orbit
  simpa only [lower65] using h

theorem space2611_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 134, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 31), (134, 252), (69, 255), (39, 22), (17, 148), (10, 150)]
    (codeMat 94) (codeMat 253) (codeMat 415) true
    det94 det253 inv253
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2611_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2611_orbit
  simpa only [lower35] using h

theorem space2612_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [260, 134, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(260, 1), (134, 68), (69, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 93) (codeMat 204) (codeMat 114) false
    det93 det204 inv204
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2612_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2612_orbit
  simpa only [lower29] using h

theorem space2613_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 133, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 136), (133, 104), (69, 232), (36, 3), (17, 148), (10, 150)]
    (codeMat 299) (codeMat 236) (codeMat 123) false
    det299 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2613_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2613_orbit
  simpa only [lower35] using h

theorem space2614_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 129, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 31), (129, 224), (69, 252), (36, 9), (17, 96), (10, 104)]
    (codeMat 115) (codeMat 236) (codeMat 123) true
    det115 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2614_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2614_orbit
  simpa only [lower35] using h

theorem space2615_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 134, 69, 35, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 139), (134, 252), (69, 245), (35, 136), (17, 104), (10, 96)]
    (codeMat 158) (codeMat 229) (codeMat 187) false
    det158 det229 inv229
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2615_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 134, 69, 35, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2615_orbit
  simpa only [lower35] using h

theorem space2616_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 128, 69, 34, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (128, 260), (69, 238), (34, 480), (17, 176), (10, 160)]
    (codeMat 158) (codeMat 236) (codeMat 123) false
    det158 det236 inv236
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2616_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 69, 34, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2616_orbit
  simpa only [lower65] using h

theorem space2617_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 160, 67, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 27), (160, 10), (67, 420), (16, 16), (10, 160), (7, 320)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    det86 det116 inv116
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2617_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 67, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2617_orbit
  simpa only [lower65] using h

theorem space2618_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 128, 82, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 17), (128, 27), (82, 255), (51, 176), (10, 480), (6, 16)]
    (codeMat 205) (codeMat 95) (codeMat 244) false
    det205 det95 inv95
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2618_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 82, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2618_orbit
  simpa only [lower65] using h

theorem space2619_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 146, 82, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 270), (146, 260), (82, 287), (50, 160), (10, 480), (6, 16)]
    (codeMat 141) (codeMat 489) (codeMat 241) false
    det141 det489 inv489
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2619_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 146, 82, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2619_orbit
  simpa only [lower65] using h

theorem space2620_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 162, 67, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 347), (162, 238), (67, 420), (17, 176), (10, 160), (6, 320)]
    (codeMat 94) (codeMat 244) (codeMat 95) false
    det94 det244 inv244
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2620_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 162, 67, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2620_orbit
  simpa only [lower65] using h

theorem space2621_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 160, 66, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 255), (160, 170), (66, 420), (16, 16), (10, 160), (6, 320)]
    (codeMat 87) (codeMat 372) (codeMat 93) false
    det87 det372 inv372
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2621_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 160, 66, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2621_orbit
  simpa only [lower65] using h

theorem space2622_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [385, 81, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(385, 20), (81, 235), (48, 3), (9, 8), (5, 128), (3, 130)]
    (codeMat 267) (codeMat 442) (codeMat 334) true
    det267 det442 inv442
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2622_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 81, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2622_orbit
  simpa only [lower35] using h

theorem space2623_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [293, 133, 65, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(293, 22), (133, 105), (65, 130), (21, 96), (8, 128), (2, 8)]
    (codeMat 143) (codeMat 298) (codeMat 270) false
    det143 det298 inv298
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2623_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 133, 65, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2623_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
