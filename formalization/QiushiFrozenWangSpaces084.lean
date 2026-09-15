import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2688_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 129, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 226), (129, 374), (80, 413), (49, 96), (8, 360), (4, 128), (2, 384)]
    (codeMat 95) (codeMat 241) (codeMat 489) false
    det95 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2688_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 129, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2688_orbit
  simpa only [lower14] using h

theorem space2689_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 128, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 150), (128, 2), (80, 149), (49, 96), (8, 360), (4, 384), (2, 128)]
    (codeMat 92) (codeMat 369) (codeMat 377) false
    det92 det369 inv369
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2689_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 128, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2689_orbit
  simpa only [lower14] using h

theorem space2690_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 134, 70, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 287), (134, 252), (70, 245), (38, 224), (18, 256), (10, 264), (1, 360)]
    (codeMat 214) (codeMat 485) (codeMat 171) false
    det214 det485 inv485
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2690_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 134, 70, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2690_orbit
  simpa only [lower14] using h

theorem space2691_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 129, 65, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (129, 324), (65, 1), (32, 24), (21, 160), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 165) (codeMat 163) false
    det85 det165 inv165
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2691_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 65, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2691_orbit
  simpa only [lower10] using h

theorem space2692_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 68, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 22), (132, 29), (68, 20), (36, 384), (16, 360), (9, 256), (3, 8)]
    (codeMat 205) (codeMat 482) (codeMat 143) false
    det205 det482 inv482
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2692_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2692_orbit
  simpa only [lower14] using h

theorem space2693_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 64, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 138), (132, 235), (64, 8), (36, 3), (20, 363), (9, 1), (3, 511)]
    (codeMat 419) (codeMat 181) (codeMat 423) false
    det419 det181 inv181
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2693_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 64, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2693_orbit
  simpa only [lower14] using h

theorem space2694_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 65, 36, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 2), (132, 327), (65, 3), (36, 16), (21, 440), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 187) (codeMat 229) false
    det93 det187 inv187
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2694_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 36, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2694_orbit
  simpa only [lower10] using h

theorem space2695_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [260, 130, 65, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(260, 4), (130, 2), (65, 7), (32, 256), (21, 88), (10, 336)]
    (codeMat 157) (codeMat 345) (codeMat 345) false
    det157 det345 inv345
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space2695_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 65, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 25 space2695_orbit
  simpa only [lower25] using h

theorem space2696_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 128, 65, 32, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 70), (128, 325), (65, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 419) (codeMat 183) false
    det93 det419 inv419
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2696_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 32, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2696_orbit
  simpa only [lower10] using h

theorem space2697_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 132, 65, 32, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 326), (132, 71), (65, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 443) (codeMat 254) false
    det93 det443 inv443
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2697_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 65, 32, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2697_orbit
  simpa only [lower10] using h

theorem space2698_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 134, 70, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (134, 508), (70, 509), (38, 480), (18, 256), (10, 264), (1, 360)]
    (codeMat 212) (codeMat 229) (codeMat 187) false
    det212 det229 inv229
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2698_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 134, 70, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2698_orbit
  simpa only [lower14] using h

theorem space2699_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 64, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 208), (130, 216), (64, 32), (32, 2), (16, 3), (10, 196), (4, 128)]
    (codeMat 98) (codeMat 114) (codeMat 204) false
    det98 det114 inv114
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2699_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2699_orbit
  simpa only [lower11] using h

theorem space2700_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 65, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 208), (130, 32), (65, 40), (32, 130), (17, 68), (10, 69), (4, 128)]
    (codeMat 107) (codeMat 225) (codeMat 169) false
    det107 det225 inv225
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2700_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2700_orbit
  simpa only [lower11] using h

theorem space2701_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 97), (131, 284), (65, 511), (32, 9), (17, 28), (10, 31), (4, 8)]
    (codeMat 459) (codeMat 205) (codeMat 242) false
    det459 det205 inv205
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2701_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space2701_orbit
  simpa only [lower14] using h

theorem space2702_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 2), (128, 3), (66, 198), (34, 208), (18, 216), (10, 240), (4, 128)]
    (codeMat 84) (codeMat 122) (codeMat 460) false
    det84 det122 inv122
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2702_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2702_orbit
  simpa only [lower11] using h

theorem space2703_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 66, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 130), (129, 196), (66, 199), (35, 80), (18, 32), (10, 248), (4, 128)]
    (codeMat 93) (codeMat 233) (codeMat 233) false
    det93 det233 inv233
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2703_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2703_orbit
  simpa only [lower11] using h

theorem space2704_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 65, 32, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 228), (130, 9), (65, 54), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 87) (codeMat 330) (codeMat 394) false
    det87 det330 inv330
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2704_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 32, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2704_orbit
  simpa only [lower11] using h

theorem space2705_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 131, 67, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (131, 70), (67, 71), (32, 24), (18, 432), (10, 440), (5, 256)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    det84 det253 inv253
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2705_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space2705_orbit
  simpa only [lower10] using h

theorem space2706_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 20), (131, 23), (67, 21), (35, 276), (18, 511), (10, 381), (5, 8)]
    (codeMat 396) (codeMat 467) (codeMat 339) false
    det396 det467 inv467
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2706_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space2706_orbit
  simpa only [lower14] using h

theorem space2707_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 34, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    det84 det110 inv110
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2707_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2707_orbit
  simpa only [lower11] using h

theorem space2708_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 28), (129, 29), (64, 3), (32, 256), (18, 360), (10, 232), (6, 8)]
    (codeMat 140) (codeMat 395) (codeMat 474) false
    det140 det395 inv395
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2708_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space2708_orbit
  simpa only [lower14] using h

theorem space2709_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 67, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 196), (130, 1), (67, 71), (32, 32), (16, 8), (10, 120), (7, 128)]
    (codeMat 85) (codeMat 331) (codeMat 410) false
    det85 det331 inv331
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2709_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2709_orbit
  simpa only [lower11] using h

theorem space2710_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 129, 66, 32, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 131), (129, 70), (66, 71), (32, 216), (17, 112), (10, 120), (7, 128)]
    (codeMat 93) (codeMat 253) (codeMat 415) false
    det93 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2710_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 32, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2710_orbit
  simpa only [lower11] using h

theorem space2711_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 66, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 216), (129, 112), (66, 120), (35, 131), (17, 70), (10, 71), (7, 128)]
    (codeMat 107) (codeMat 253) (codeMat 415) false
    det107 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2711_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2711_orbit
  simpa only [lower11] using h

theorem space2712_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 66, 35, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 136), (130, 32), (66, 248), (35, 129), (17, 196), (10, 199), (7, 128)]
    (codeMat 107) (codeMat 205) (codeMat 242) false
    det107 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2712_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 35, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2712_orbit
  simpa only [lower11] using h

theorem space2713_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 65, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 182), (128, 219), (65, 63), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 87) (codeMat 379) (codeMat 247) false
    det87 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2713_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2713_orbit
  simpa only [lower11] using h

theorem space2714_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 129, 65, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 137), (129, 228), (65, 63), (35, 136), (18, 32), (10, 248), (7, 128)]
    (codeMat 94) (codeMat 205) (codeMat 242) false
    det94 det205 inv205
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2714_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space2714_orbit
  simpa only [lower11] using h

theorem space2715_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 64, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 112), (128, 40), (64, 32), (34, 198), (17, 69), (10, 68), (5, 128)]
    (codeMat 99) (codeMat 482) (codeMat 143) false
    det99 det482 inv482
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2715_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2715_orbit
  simpa only [lower11] using h

theorem space2716_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 264), (130, 384), (64, 360), (34, 20), (17, 30), (10, 29), (5, 8)]
    (codeMat 331) (codeMat 465) (codeMat 465) false
    det331 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2716_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space2716_orbit
  simpa only [lower14] using h

theorem space2717_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 67, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 259), (130, 1), (67, 71), (33, 280), (18, 8), (10, 440), (5, 256)]
    (codeMat 93) (codeMat 111) (codeMat 412) false
    det93 det111 inv111
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2717_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space2717_orbit
  simpa only [lower10] using h

theorem space2718_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 67, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 255), (128, 9), (67, 137), (35, 406), (18, 8), (10, 138), (5, 511)]
    (codeMat 351) (codeMat 267) (codeMat 282) false
    det351 det267 inv267
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2718_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space2718_orbit
  simpa only [lower14] using h

theorem space2719_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 387), (128, 1), (65, 384), (33, 235), (18, 8), (10, 503), (7, 130)]
    (codeMat 348) (codeMat 334) (codeMat 442) false
    det348 det334 inv334
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2719_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space2719_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
