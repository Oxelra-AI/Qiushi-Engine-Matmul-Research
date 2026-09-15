import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2208_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [288, 145, 67, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(288, 32), (145, 42), (67, 175), (10, 173), (7, 9)]
    (codeMat 247) (codeMat 410) (codeMat 331) false
    det247 det410 inv410
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2208_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 145, 67, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space2208_orbit
  simpa only [lower103] using h

theorem space2209_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 144, 67, 51, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 119), (144, 130), (67, 235), (51, 255), (10, 227), (7, 3)]
    (codeMat 183) (codeMat 426) (codeMat 335) true
    det183 det426 inv426
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2209_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 144, 67, 51, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space2209_orbit
  simpa only [lower35] using h

theorem space2210_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [385, 67, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(385, 42), (67, 173), (48, 32), (10, 164), (7, 2)]
    (codeMat 143) (codeMat 425) (codeMat 249) true
    det143 det425 inv425
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2210_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 67, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space2210_orbit
  simpa only [lower103] using h

theorem space2211_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [384, 67, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(384, 40), (67, 175), (49, 34), (10, 166), (7, 2)]
    (codeMat 207) (codeMat 409) (codeMat 473) true
    det207 det409 inv409
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2211_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 67, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space2211_orbit
  simpa only [lower103] using h

theorem space2212_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [272, 160, 66, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(272, 68), (160, 69), (66, 170), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    det142 det394 inv394
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2212_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 160, 66, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 29 space2212_orbit
  simpa only [lower29] using h

theorem space2213_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 129, 68, 37, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 451), (129, 262), (68, 196), (37, 280), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    det92 det244 inv244
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2213_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 68, 37, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space2213_orbit
  simpa only [lower17] using h

theorem space2214_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 129, 68, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 329), (129, 274), (68, 100), (37, 328), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    det86 det84 inv84
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2214_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 68, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space2214_orbit
  simpa only [lower17] using h

theorem space2215_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 144, 64, 48, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (144, 325), (64, 2), (48, 256), (10, 168), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    det140 det142 inv142
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2215_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 64, 48, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2215_orbit
  simpa only [lower10] using h

theorem space2216_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 128, 64, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 158), (128, 3), (64, 1), (48, 360), (9, 8), (4, 384), (3, 128)]
    (codeMat 92) (codeMat 307) (codeMat 311) false
    det92 det307 inv307
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2216_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 128, 64, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2216_orbit
  simpa only [lower14] using h

theorem space2217_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 132, 68, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 219), (132, 210), (68, 228), (36, 216), (20, 208), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    det86 det116 inv116
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2217_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2217_orbit
  simpa only [lower11] using h

theorem space2218_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 132, 68, 32, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 3), (132, 198), (68, 196), (32, 216), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    det92 det244 inv244
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2218_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2218_orbit
  simpa only [lower11] using h

theorem space2219_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 129, 68, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (129, 191), (68, 237), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 499) (codeMat 382) false
    det94 det499 inv499
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2219_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2219_orbit
  simpa only [lower11] using h

theorem space2220_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 68, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 100), (129, 191), (68, 109), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 467) (codeMat 339) false
    det94 det467 inv467
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2220_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2220_orbit
  simpa only [lower11] using h

theorem space2221_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 133, 68, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 100), (133, 210), (68, 109), (32, 32), (21, 80), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 337) (codeMat 337) false
    det87 det337 inv337
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2221_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 68, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2221_orbit
  simpa only [lower11] using h

theorem space2222_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 133, 68, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (133, 82), (68, 237), (37, 240), (21, 208), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 369) (codeMat 377) false
    det87 det369 inv369
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2222_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2222_orbit
  simpa only [lower11] using h

theorem space2223_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 64, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 210), (130, 219), (64, 54), (34, 208), (18, 216), (10, 240), (4, 128)]
    (codeMat 86) (codeMat 122) (codeMat 460) false
    det86 det122 inv122
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2223_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2223_orbit
  simpa only [lower11] using h

theorem space2224_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 65, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 112), (128, 216), (65, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 106) (codeMat 370) (codeMat 207) false
    det106 det370 inv370
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2224_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2224_orbit
  simpa only [lower11] using h

theorem space2225_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 66, 32, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 88), (128, 8), (66, 112), (32, 3), (16, 1), (10, 70), (6, 128)]
    (codeMat 98) (codeMat 110) (codeMat 444) false
    det98 det110 inv110
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2225_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2225_orbit
  simpa only [lower11] using h

theorem space2226_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 67, 34, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 112), (128, 216), (67, 248), (34, 198), (16, 3), (10, 199), (7, 128)]
    (codeMat 106) (codeMat 379) (codeMat 247) false
    det106 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2226_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 34, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2226_orbit
  simpa only [lower11] using h

theorem space2227_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 67, 34, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 160), (130, 8), (67, 120), (34, 68), (16, 1), (10, 71), (7, 128)]
    (codeMat 106) (codeMat 331) (codeMat 410) false
    det106 det331 inv331
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2227_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 34, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2227_orbit
  simpa only [lower11] using h

theorem space2228_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 65, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 112), (129, 248), (65, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 107) (codeMat 498) (codeMat 206) false
    det107 det498 inv498
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2228_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2228_orbit
  simpa only [lower11] using h

theorem space2229_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 65, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 100), (129, 237), (65, 54), (33, 160), (18, 40), (10, 240), (5, 128)]
    (codeMat 94) (codeMat 458) (codeMat 458) false
    det94 det458 inv458
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2229_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2229_orbit
  simpa only [lower11] using h

theorem space2230_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 64, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 210), (131, 228), (64, 63), (35, 80), (18, 32), (10, 248), (4, 128)]
    (codeMat 95) (codeMat 233) (codeMat 233) false
    det95 det233 inv233
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2230_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2230_orbit
  simpa only [lower11] using h

theorem space2231_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 67, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 8), (128, 32), (67, 248), (35, 129), (17, 196), (10, 199), (7, 128)]
    (codeMat 99) (codeMat 205) (codeMat 242) false
    det99 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2231_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2231_orbit
  simpa only [lower11] using h

theorem space2232_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 67, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 88), (131, 112), (67, 120), (35, 131), (17, 70), (10, 71), (7, 128)]
    (codeMat 99) (codeMat 253) (codeMat 415) false
    det99 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2232_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2232_orbit
  simpa only [lower11] using h

theorem space2233_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 67, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (131, 196), (67, 199), (35, 136), (18, 32), (10, 248), (7, 128)]
    (codeMat 92) (codeMat 205) (codeMat 242) false
    det92 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2233_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2233_orbit
  simpa only [lower11] using h

theorem space2234_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 129, 66, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 160), (129, 112), (66, 120), (33, 196), (17, 70), (10, 71), (6, 128)]
    (codeMat 107) (codeMat 473) (codeMat 409) false
    det107 det473 inv473
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2234_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2234_orbit
  simpa only [lower11] using h

theorem space2235_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 66, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (129, 196), (66, 199), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 93) (codeMat 489) (codeMat 241) false
    det93 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2235_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2235_orbit
  simpa only [lower11] using h

theorem space2236_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 131, 64, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 68), (131, 326), (64, 325), (34, 416), (18, 432), (10, 424), (4, 256)]
    (codeMat 85) (codeMat 465) (codeMat 465) false
    det85 det465 inv465
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2236_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space2236_orbit
  simpa only [lower10] using h

theorem space2237_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 64, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 68), (130, 3), (64, 325), (35, 160), (18, 24), (10, 424), (4, 256)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    det93 det339 inv339
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2237_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space2237_orbit
  simpa only [lower10] using h

theorem space2238_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 80), (128, 8), (64, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    det98 det98 inv98
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2238_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2238_orbit
  simpa only [lower11] using h

theorem space2239_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 64, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 80), (128, 32), (64, 40), (32, 130), (17, 68), (10, 69), (4, 128)]
    (codeMat 99) (codeMat 225) (codeMat 169) false
    det99 det225 inv225
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2239_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2239_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
