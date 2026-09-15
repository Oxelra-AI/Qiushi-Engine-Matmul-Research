import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2720_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 67, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 240), (128, 32), (67, 248), (33, 70), (17, 196), (10, 199), (6, 128)]
    (codeMat 99) (codeMat 489) (codeMat 241) false
    det99 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2720_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2720_orbit
  simpa only [lower11] using h

theorem space2721_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 67, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 32), (131, 112), (67, 120), (33, 196), (17, 70), (10, 71), (6, 128)]
    (codeMat 99) (codeMat 473) (codeMat 409) false
    det99 det473 inv473
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2721_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2721_orbit
  simpa only [lower11] using h

theorem space2722_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 67, 34, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 68), (131, 70), (67, 71), (34, 160), (17, 112), (10, 120), (6, 128)]
    (codeMat 92) (codeMat 473) (codeMat 409) false
    det92 det473 inv473
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2722_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 34, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2722_orbit
  simpa only [lower11] using h

theorem space2723_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 130, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 119), (130, 9), (70, 245), (34, 392), (18, 8), (10, 264), (1, 360)]
    (codeMat 158) (codeMat 359) (codeMat 174) false
    det158 det359 inv359
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2723_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2723_orbit
  simpa only [lower14] using h

theorem space2724_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 160, 64, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (160, 68), (64, 2), (16, 256), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    det140 det140 inv140
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2724_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2724_orbit
  simpa only [lower10] using h

theorem space2725_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 160, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 31), (160, 224), (66, 23), (18, 511), (10, 151), (4, 3), (1, 2)]
    (codeMat 417) (codeMat 190) (codeMat 355) false
    det417 det190 inv190
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2725_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 160, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2725_orbit
  simpa only [lower14] using h

theorem space2726_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [290, 128, 66, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(290, 22), (128, 130), (66, 81), (16, 128), (10, 80), (6, 32), (1, 8)]
    (codeMat 142) (codeMat 305) (codeMat 305) false
    det142 det305 inv305
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2726_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 128, 66, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2726_orbit
  simpa only [lower11] using h

theorem space2727_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [386, 66, 32, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(386, 69), (66, 197), (32, 32), (16, 40), (10, 29), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 395) (codeMat 474) false
    det273 det395 inv395
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2727_lower : 12 ≤ frozenWangTable.L0 (spanCodes [386, 66, 32, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2727_orbit
  simpa only [lower11] using h

theorem space2728_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (160, 224), (64, 128), (18, 511), (10, 151), (6, 3), (1, 2)]
    (codeMat 305) (codeMat 410) (codeMat 331) false
    det305 det410 inv410
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2728_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2728_orbit
  simpa only [lower14] using h

theorem space2729_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 224), (130, 128), (64, 360), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 334) (codeMat 117) (codeMat 380) false
    det334 det117 inv117
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2729_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space2729_orbit
  simpa only [lower14] using h

theorem space2730_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 64, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 392), (131, 488), (64, 360), (35, 406), (18, 511), (10, 381), (6, 8)]
    (codeMat 335) (codeMat 499) (codeMat 382) false
    det335 det499 inv499
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2730_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space2730_orbit
  simpa only [lower14] using h

theorem space2731_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 64, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (131, 228), (64, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 95) (codeMat 489) (codeMat 241) false
    det95 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2731_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space2731_orbit
  simpa only [lower11] using h

theorem space2732_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 23), (131, 29), (65, 3), (34, 488), (18, 360), (10, 232), (7, 8)]
    (codeMat 141) (codeMat 431) (codeMat 477) false
    det141 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2732_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space2732_orbit
  simpa only [lower14] using h

theorem space2733_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 65, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 488), (131, 480), (65, 256), (35, 362), (18, 3), (10, 508), (7, 360)]
    (codeMat 355) (codeMat 114) (codeMat 204) false
    det355 det114 inv114
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2733_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space2733_orbit
  simpa only [lower14] using h

theorem space2734_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 65, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (128, 3), (65, 325), (35, 272), (18, 24), (10, 424), (7, 256)]
    (codeMat 92) (codeMat 115) (codeMat 492) false
    det92 det115 inv115
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2734_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2734_orbit
  simpa only [lower10] using h

theorem space2735_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 66, 32, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 326), (130, 325), (66, 327), (32, 432), (17, 168), (10, 184), (7, 256)]
    (codeMat 92) (codeMat 491) (codeMat 375) false
    det92 det491 inv491
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2735_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2735_orbit
  simpa only [lower10] using h

theorem space2736_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 129, 66, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 324), (129, 70), (66, 71), (34, 416), (18, 432), (10, 440), (4, 256)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    det85 det473 inv473
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2736_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space2736_orbit
  simpa only [lower10] using h

theorem space2737_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 404), (128, 9), (66, 119), (33, 276), (18, 8), (10, 503), (4, 130)]
    (codeMat 415) (codeMat 106) (codeMat 396) false
    det415 det106 inv106
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2737_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space2737_orbit
  simpa only [lower14] using h

theorem space2738_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 23), (66, 21), (33, 105), (18, 511), (10, 381), (4, 8)]
    (codeMat 461) (codeMat 215) (codeMat 342) false
    det461 det215 inv215
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2738_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space2738_orbit
  simpa only [lower14] using h

theorem space2739_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 33, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (131, 224), (65, 256), (33, 97), (17, 227), (10, 284), (4, 8)]
    (codeMat 335) (codeMat 86) (codeMat 212) false
    det335 det86 inv86
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2739_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space2739_orbit
  simpa only [lower14] using h

theorem space2740_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 67, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 68), (130, 3), (67, 198), (32, 32), (18, 216), (10, 240), (5, 128)]
    (codeMat 85) (codeMat 346) (codeMat 459) false
    det85 det346 inv346
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2740_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2740_orbit
  simpa only [lower11] using h

theorem space2741_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 64, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 240), (131, 248), (64, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 99) (codeMat 498) (codeMat 206) false
    det99 det498 inv498
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2741_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2741_orbit
  simpa only [lower11] using h

theorem space2742_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 362), (130, 3), (64, 511), (33, 488), (17, 480), (10, 224), (5, 360)]
    (codeMat 213) (codeMat 123) (codeMat 236) false
    det213 det123 inv123
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2742_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space2742_orbit
  simpa only [lower14] using h

theorem space2743_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 64, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 100), (128, 63), (64, 54), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 95) (codeMat 474) (codeMat 395) false
    det95 det474 inv474
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2743_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2743_orbit
  simpa only [lower11] using h

theorem space2744_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (132, 68), (65, 3), (37, 424), (21, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 397) (codeMat 250) false
    det85 det397 inv397
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2744_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2744_orbit
  simpa only [lower10] using h

theorem space2745_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 129, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 71), (129, 324), (65, 1), (37, 440), (21, 416), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 421) (codeMat 179) false
    det85 det421 inv421
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2745_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2745_orbit
  simpa only [lower10] using h

theorem space2746_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 128, 69, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 22), (128, 1), (69, 20), (32, 384), (17, 96), (8, 256), (2, 8)]
    (codeMat 140) (codeMat 354) (codeMat 142) false
    det140 det354 inv354
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2746_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2746_orbit
  simpa only [lower14] using h

theorem space2747_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 144, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 163), (144, 1), (80, 324), (49, 160), (8, 256), (4, 24), (2, 8)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    det142 det102 inv102
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2747_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 144, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2747_orbit
  simpa only [lower10] using h

theorem space2748_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 29), (128, 8), (80, 96), (49, 149), (8, 360), (4, 3), (2, 1)]
    (codeMat 417) (codeMat 103) (codeMat 188) false
    det417 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2748_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2748_orbit
  simpa only [lower14] using h

theorem space2749_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 144, 80, 33, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 162), (144, 1), (80, 324), (33, 160), (8, 256), (4, 16), (2, 8)]
    (codeMat 142) (codeMat 98) (codeMat 140) false
    det142 det98 inv98
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2749_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 80, 33, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2749_orbit
  simpa only [lower10] using h

theorem space2750_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 160, 65, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 502), (160, 276), (65, 9), (17, 96), (8, 8), (4, 384), (2, 256)]
    (codeMat 87) (codeMat 417) (codeMat 177) false
    det87 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2750_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 160, 65, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2750_orbit
  simpa only [lower14] using h

theorem space2751_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 64, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (160, 28), (64, 1), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 165) (codeMat 163) false
    det84 det165 inv165
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2751_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2751_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
