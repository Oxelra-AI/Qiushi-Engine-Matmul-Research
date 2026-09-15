import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2496_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 81, 33, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 252), (81, 232), (33, 11), (9, 8), (5, 2), (3, 128)]
    (codeMat 267) (codeMat 188) (codeMat 103) true
    det267 det188 inv188
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2496_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 81, 33, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2496_orbit
  simpa only [lower35] using h

theorem space2497_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 81, 32, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 96), (81, 118), (32, 8), (8, 9), (5, 2), (2, 128)]
    (codeMat 266) (codeMat 169) (codeMat 225) true
    det266 det169 inv169
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2497_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 81, 32, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2497_orbit
  simpa only [lower35] using h

theorem space2498_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 80, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 126), (80, 232), (32, 8), (10, 30), (4, 1), (1, 3)]
    (codeMat 401) (codeMat 157) (codeMat 486) false
    det401 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2498_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 80, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2498_orbit
  simpa only [lower35] using h

theorem space2499_orbit :
    frozenWangTable.OrbitImage 141 (spanCodes [307, 179, 81, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 141 [(307, 266), (179, 298), (81, 118), (10, 383), (5, 2)]
    (codeMat 271) (codeMat 489) (codeMat 241) true
    det271 det489 inv489
    (by rw [basis141]; decide +kernel)
    (by rw [basis141]; decide +kernel)

theorem space2499_lower : 15 ≤ frozenWangTable.L0 (spanCodes [307, 179, 81, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 141 space2499_orbit
  simpa only [lower141] using h

theorem space2500_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [292, 160, 84, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(292, 1), (160, 209), (84, 379), (8, 36), (2, 192)]
    (codeMat 111) (codeMat 86) (codeMat 212) false
    det111 det86 inv86
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space2500_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 160, 84, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 220 space2500_orbit
  simpa only [lower220] using h

theorem space2501_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [292, 164, 70, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(292, 27), (164, 26), (70, 78), (18, 16), (10, 272)]
    (codeMat 156) (codeMat 124) (codeMat 124) false
    det156 det124 inv124
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space2501_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 70, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space2501_orbit
  simpa only [lower149] using h

theorem space2502_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 65, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 22), (128, 9), (65, 2), (21, 96), (8, 128), (2, 8)]
    (codeMat 141) (codeMat 298) (codeMat 270) false
    det141 det298 inv298
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2502_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2502_orbit
  simpa only [lower35] using h

theorem space2503_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 129, 65, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 20), (129, 11), (65, 2), (21, 232), (9, 128), (3, 8)]
    (codeMat 205) (codeMat 282) (codeMat 267) false
    det205 det282 inv282
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2503_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2503_orbit
  simpa only [lower35] using h

theorem space2504_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [292, 165, 70, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(292, 325), (165, 266), (70, 78), (18, 16), (10, 272)]
    (codeMat 157) (codeMat 348) (codeMat 125) false
    det157 det348 inv348
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space2504_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 165, 70, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space2504_orbit
  simpa only [lower149] using h

theorem space2505_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [256, 133, 66, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(256, 438), (133, 284), (66, 138), (22, 413), (10, 139)]
    (codeMat 494) (codeMat 307) (codeMat 311) false
    det494 det307 inv307
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space2505_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 66, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 189 space2505_orbit
  simpa only [lower189] using h

theorem space2506_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [288, 166, 70, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(288, 1), (166, 26), (70, 350), (18, 16), (10, 272)]
    (codeMat 158) (codeMat 92) (codeMat 116) false
    det158 det92 inv92
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space2506_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 70, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space2506_orbit
  simpa only [lower149] using h

theorem space2507_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [289, 167, 70, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(289, 79), (167, 266), (70, 350), (18, 16), (10, 272)]
    (codeMat 159) (codeMat 380) (codeMat 117) false
    det159 det380 inv380
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space2507_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 167, 70, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space2507_orbit
  simpa only [lower149] using h

theorem space2508_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [294, 160, 70, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(294, 507), (160, 480), (70, 11), (18, 260), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 421) (codeMat 179) false
    det161 det421 inv421
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2508_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 160, 70, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space2508_orbit
  simpa only [lower65] using h

theorem space2509_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [308, 160, 84, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(308, 350), (160, 53), (84, 379), (8, 36), (2, 192)]
    (codeMat 102) (codeMat 342) (codeMat 215) false
    det102 det342 inv342
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space2509_lower : 15 ≤ frozenWangTable.L0 (spanCodes [308, 160, 84, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 220 space2509_orbit
  simpa only [lower220] using h

theorem space2510_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [262, 134, 67, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(262, 316), (134, 284), (67, 138), (23, 413), (10, 139)]
    (codeMat 423) (codeMat 311) (codeMat 307) false
    det423 det311 inv311
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space2510_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 67, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 189 space2510_orbit
  simpa only [lower189] using h

theorem space2511_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [292, 160, 70, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(292, 27), (160, 480), (70, 79), (18, 260), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 165) (codeMat 163) false
    det177 det165 inv165
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2511_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 160, 70, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space2511_orbit
  simpa only [lower65] using h

theorem space2512_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [274, 148, 84, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(274, 132), (148, 164), (84, 481), (39, 367), (10, 366)]
    (codeMat 491) (codeMat 185) (codeMat 481) false
    det491 det185 inv185
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space2512_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 148, 84, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 197 space2512_orbit
  simpa only [lower197] using h

theorem space2513_orbit :
    frozenWangTable.OrbitImage 112 (spanCodes [262, 146, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 112 [(262, 371), (146, 9), (84, 377), (53, 272), (10, 274)]
    (codeMat 159) (codeMat 351) (codeMat 239) true
    det159 det351 inv351
    (by rw [basis112]; decide +kernel)
    (by rw [basis112]; decide +kernel)

theorem space2513_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 146, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 112 space2513_orbit
  simpa only [lower112] using h

theorem space2514_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [274, 148, 84, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(274, 11), (148, 139), (84, 171), (36, 1), (10, 295)]
    (codeMat 355) (codeMat 95) (codeMat 244) false
    det355 det95 inv95
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space2514_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 148, 84, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space2514_orbit
  simpa only [lower187] using h

theorem space2515_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [273, 134, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(273, 335), (134, 164), (84, 143), (53, 367), (10, 366)]
    (codeMat 379) (codeMat 409) (codeMat 473) false
    det379 det409 inv409
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space2515_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 134, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 197 space2515_orbit
  simpa only [lower197] using h

theorem space2516_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [260, 144, 84, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(260, 32), (144, 325), (84, 165), (48, 1), (10, 366)]
    (codeMat 298) (codeMat 458) (codeMat 458) false
    det298 det458 inv458
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space2516_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 144, 84, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 197 space2516_orbit
  simpa only [lower197] using h

theorem space2517_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 147, 80, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 261), (147, 447), (80, 446), (48, 16), (10, 496), (4, 320)]
    (codeMat 85) (codeMat 478) (codeMat 445) false
    det85 det478 inv478
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2517_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 147, 80, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space2517_orbit
  simpa only [lower65] using h

theorem space2518_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 130, 81, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 158), (130, 3), (81, 28), (50, 232), (10, 224), (5, 128)]
    (codeMat 85) (codeMat 370) (codeMat 207) false
    det85 det370 inv370
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2518_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 130, 81, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2518_orbit
  simpa only [lower35] using h

theorem space2519_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 146, 83, 35, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 26), (146, 1), (83, 446), (35, 336), (10, 496), (7, 320)]
    (codeMat 95) (codeMat 106) (codeMat 396) false
    det95 det106 inv106
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2519_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 146, 83, 35, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2519_orbit
  simpa only [lower65] using h

theorem space2520_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 130, 80, 33, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 68), (130, 260), (80, 160), (33, 78), (10, 436), (4, 1)]
    (codeMat 305) (codeMat 204) (codeMat 114) false
    det305 det204 inv204
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2520_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 80, 33, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space2520_orbit
  simpa only [lower65] using h

theorem space2521_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 128, 80, 35, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 10), (128, 1), (80, 79), (35, 160), (10, 496), (4, 16)]
    (codeMat 204) (codeMat 107) (codeMat 428) false
    det204 det107 inv107
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2521_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 80, 35, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space2521_orbit
  simpa only [lower65] using h

theorem space2522_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 130, 80, 34, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 170), (130, 260), (80, 255), (34, 160), (10, 480), (4, 16)]
    (codeMat 143) (codeMat 233) (codeMat 233) false
    det143 det233 inv233
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2522_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 80, 34, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space2522_orbit
  simpa only [lower65] using h

theorem space2523_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 129, 83, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 331), (129, 446), (83, 79), (48, 320), (10, 496), (7, 16)]
    (codeMat 142) (codeMat 253) (codeMat 415) false
    det142 det253 inv253
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2523_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 129, 83, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2523_orbit
  simpa only [lower65] using h

theorem space2524_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [402, 82, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(402, 127), (82, 255), (48, 8), (10, 31), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 443) (codeMat 254) false
    det273 det443 inv443
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2524_lower : 15 ≤ frozenWangTable.L0 (spanCodes [402, 82, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2524_orbit
  simpa only [lower35] using h

theorem space2525_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 146, 83, 34, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 124), (146, 3), (83, 245), (34, 224), (10, 232), (7, 128)]
    (codeMat 87) (codeMat 339) (codeMat 467) false
    det87 det339 inv339
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2525_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 146, 83, 34, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space2525_orbit
  simpa only [lower35] using h

theorem space2526_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 129, 83, 35, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 137), (129, 246), (83, 29), (35, 136), (10, 232), (7, 128)]
    (codeMat 94) (codeMat 213) (codeMat 470) false
    det94 det213 inv213
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2526_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 83, 35, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space2526_orbit
  simpa only [lower35] using h

theorem space2527_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 147, 80, 49, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 130), (147, 246), (80, 245), (49, 96), (10, 232), (4, 128)]
    (codeMat 93) (codeMat 241) (codeMat 489) false
    det93 det241 inv241
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2527_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 147, 80, 49, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2527_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
