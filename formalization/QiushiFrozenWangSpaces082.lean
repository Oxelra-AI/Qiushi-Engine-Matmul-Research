import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2624_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [385, 80, 48, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(385, 20), (80, 97), (48, 1), (8, 8), (4, 128), (2, 130)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    det266 det394 inv394
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2624_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 80, 48, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2624_orbit
  simpa only [lower35] using h

theorem space2625_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [294, 134, 66, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(294, 136), (134, 232), (66, 29), (22, 224), (10, 28), (1, 3)]
    (codeMat 190) (codeMat 305) (codeMat 305) true
    det190 det305 inv305
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2625_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 134, 66, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2625_orbit
  simpa only [lower35] using h

theorem space2626_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [386, 82, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(386, 148), (82, 252), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 425) (codeMat 249) false
    det401 det425 inv425
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2626_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 82, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2626_orbit
  simpa only [lower35] using h

theorem space2627_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [130, 67, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(130, 1), (67, 15), (35, 304), (18, 2), (10, 34), (5, 438)]
    (codeMat 157) (codeMat 267) (codeMat 282) true
    det157 det267 inv267
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2627_lower : 14 ≤ frozenWangTable.L0 (spanCodes [130, 67, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space2627_orbit
  simpa only [lower55] using h

theorem space2628_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [273, 146, 82, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(273, 442), (146, 438), (82, 406), (33, 133), (10, 170), (6, 45)]
    (codeMat 285) (codeMat 467) (codeMat 339) true
    det285 det467 inv467
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2628_lower : 14 ≤ frozenWangTable.L0 (spanCodes [273, 146, 82, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space2628_orbit
  simpa only [lower55] using h

theorem space2629_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [273, 128, 83, 50, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(273, 318), (128, 45), (83, 287), (50, 137), (10, 139), (7, 1)]
    (codeMat 337) (codeMat 375) (codeMat 491) true
    det337 det375 inv375
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2629_lower : 14 ≤ frozenWangTable.L0 (spanCodes [273, 128, 83, 50, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space2629_orbit
  simpa only [lower55] using h

theorem space2630_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 144, 80, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 164), (144, 2), (80, 47), (48, 32), (10, 170), (4, 438)]
    (codeMat 342) (codeMat 377) (codeMat 369) false
    det342 det377 inv377
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2630_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 144, 80, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space2630_orbit
  simpa only [lower55] using h

theorem space2631_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [274, 145, 81, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(274, 164), (145, 136), (81, 168), (33, 439), (10, 440), (5, 1)]
    (codeMat 313) (codeMat 492) (codeMat 115) true
    det313 det492 inv492
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2631_lower : 14 ≤ frozenWangTable.L0 (spanCodes [274, 145, 81, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space2631_orbit
  simpa only [lower55] using h

theorem space2632_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 128, 66, 32, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 3), (128, 32), (66, 284), (32, 2), (22, 47), (10, 170)]
    (codeMat 279) (codeMat 93) (codeMat 372) true
    det279 det93 inv93
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2632_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 128, 66, 32, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space2632_orbit
  simpa only [lower55] using h

theorem space2633_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 133, 67, 36, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 408), (133, 440), (67, 136), (36, 45), (23, 441), (10, 139)]
    (codeMat 359) (codeMat 271) (codeMat 314) false
    det359 det271 inv271
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2633_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 133, 67, 36, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space2633_orbit
  simpa only [lower55] using h

theorem space2634_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 129, 66, 36, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (129, 316), (66, 284), (36, 2), (22, 133), (10, 170)]
    (codeMat 351) (codeMat 207) (codeMat 370) true
    det351 det207 inv207
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2634_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 36, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space2634_orbit
  simpa only [lower55] using h

theorem space2635_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 130, 81, 48, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 287), (130, 32), (81, 304), (48, 438), (10, 408), (5, 3)]
    (codeMat 382) (codeMat 340) (codeMat 85) true
    det382 det340 inv340
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2635_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 81, 48, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space2635_orbit
  simpa only [lower55] using h

theorem space2636_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 457), (129, 374), (64, 219), (35, 328), (17, 240), (10, 408), (5, 128)]
    (codeMat 87) (codeMat 157) (codeMat 486) false
    det87 det157 inv157
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2636_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space2636_orbit
  simpa only [lower17] using h

theorem space2637_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 67, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 91), (129, 100), (67, 329), (35, 408), (18, 32), (10, 328), (5, 128)]
    (codeMat 95) (codeMat 165) (codeMat 163) false
    det95 det165 inv165
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2637_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space2637_orbit
  simpa only [lower17] using h

theorem space2638_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 131, 66, 33, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 390), (131, 196), (66, 451), (33, 240), (16, 32), (10, 280), (6, 128)]
    (codeMat 85) (codeMat 425) (codeMat 249) false
    det85 det425 inv425
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2638_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 66, 33, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space2638_orbit
  simpa only [lower17] using h

theorem space2639_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 67, 32, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 196), (130, 390), (67, 323), (32, 32), (17, 240), (10, 408), (6, 128)]
    (codeMat 84) (codeMat 409) (codeMat 473) false
    det84 det409 inv409
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2639_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 32, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space2639_orbit
  simpa only [lower17] using h

theorem space2640_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [275, 130, 83, 34, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(275, 317), (130, 32), (83, 316), (34, 168), (10, 170), (7, 45)]
    (codeMat 340) (codeMat 337) (codeMat 337) true
    det340 det337 inv337
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2640_lower : 14 ≤ frozenWangTable.L0 (spanCodes [275, 130, 83, 34, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space2640_orbit
  simpa only [lower55] using h

theorem space2641_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 33, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 457), (131, 429), (67, 374), (33, 456), (16, 360), (10, 240), (7, 128)]
    (codeMat 94) (codeMat 206) (codeMat 498) false
    det94 det206 inv206
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2641_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 33, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2641_orbit
  simpa only [lower17] using h

theorem space2642_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 67, 35, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 197), (129, 196), (67, 451), (35, 488), (16, 32), (10, 280), (7, 128)]
    (codeMat 84) (codeMat 397) (codeMat 250) false
    det84 det397 inv397
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2642_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 35, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2642_orbit
  simpa only [lower17] using h

theorem space2643_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 66, 33, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 191), (128, 219), (66, 374), (33, 440), (17, 408), (10, 240), (7, 128)]
    (codeMat 87) (codeMat 382) (codeMat 499) false
    det87 det382 inv382
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2643_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 33, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2643_orbit
  simpa only [lower17] using h

theorem space2644_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 131, 66, 33, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 390), (131, 451), (66, 263), (33, 112), (17, 280), (10, 312), (7, 128)]
    (codeMat 93) (codeMat 379) (codeMat 247) false
    det93 det379 inv379
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2644_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 66, 33, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2644_orbit
  simpa only [lower17] using h

theorem space2645_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 131, 66, 34, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 262), (131, 263), (66, 451), (34, 112), (17, 312), (10, 280), (7, 128)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    det92 det443 inv443
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2645_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 66, 34, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2645_orbit
  simpa only [lower17] using h

theorem space2646_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 32, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 301), (130, 219), (64, 63), (32, 360), (17, 280), (10, 312), (5, 128)]
    (codeMat 95) (codeMat 351) (codeMat 239) false
    det95 det351 inv351
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2646_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 32, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space2646_orbit
  simpa only [lower17] using h

theorem space2647_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 67, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (129, 301), (67, 329), (35, 280), (18, 360), (10, 328), (5, 128)]
    (codeMat 87) (codeMat 167) (codeMat 167) false
    det87 det167 inv167
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2647_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 67, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space2647_orbit
  simpa only [lower17] using h

theorem space2648_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 65, 33, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 402), (131, 374), (65, 219), (33, 208), (17, 240), (10, 408), (4, 128)]
    (codeMat 86) (codeMat 185) (codeMat 481) false
    det86 det185 inv185
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2648_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 33, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space2648_orbit
  simpa only [lower17] using h

theorem space2649_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [289, 131, 67, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(289, 33), (131, 164), (67, 274), (19, 166), (10, 306), (4, 45)]
    (codeMat 382) (codeMat 340) (codeMat 85) false
    det382 det340 inv340
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space2649_lower : 14 ≤ frozenWangTable.L0 (spanCodes [289, 131, 67, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space2649_orbit
  simpa only [lower55] using h

theorem space2650_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 34, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 263), (128, 390), (66, 323), (34, 440), (17, 240), (10, 408), (7, 128)]
    (codeMat 85) (codeMat 445) (codeMat 478) false
    det85 det445 inv445
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2650_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 34, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2650_orbit
  simpa only [lower17] using h

theorem space2651_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 67, 35, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 68), (131, 197), (67, 323), (35, 160), (16, 360), (10, 408), (7, 128)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    det93 det395 inv395
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2651_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 35, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2651_orbit
  simpa only [lower17] using h

theorem space2652_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 66, 33, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 391), (129, 197), (66, 323), (33, 312), (16, 360), (10, 408), (6, 128)]
    (codeMat 92) (codeMat 431) (codeMat 477) false
    det92 det431 inv431
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2652_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 33, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space2652_orbit
  simpa only [lower17] using h

theorem space2653_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 263), (129, 69), (64, 1), (35, 312), (18, 360), (10, 328), (6, 128)]
    (codeMat 84) (codeMat 423) (codeMat 181) false
    det84 det423 inv423
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2653_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space2653_orbit
  simpa only [lower17] using h

theorem space2654_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 65, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 391), (131, 68), (65, 1), (33, 440), (18, 32), (10, 328), (7, 128)]
    (codeMat 93) (codeMat 421) (codeMat 179) false
    det93 det421 inv421
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2654_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2654_orbit
  simpa only [lower17] using h

theorem space2655_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 402), (131, 100), (66, 329), (33, 208), (18, 32), (10, 328), (4, 128)]
    (codeMat 94) (codeMat 161) (codeMat 161) false
    det94 det161 inv161
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2655_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space2655_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
