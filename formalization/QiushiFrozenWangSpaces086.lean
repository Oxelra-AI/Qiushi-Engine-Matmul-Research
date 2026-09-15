import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2752_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 64, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 278), (132, 119), (64, 130), (36, 384), (20, 392), (9, 128), (3, 360)]
    (codeMat 215) (codeMat 442) (codeMat 334) false
    det215 det442 inv442
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2752_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 64, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2752_orbit
  simpa only [lower14] using h

theorem space2753_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 128, 65, 36, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 2), (128, 325), (65, 1), (36, 16), (21, 424), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 163) (codeMat 165) false
    det93 det163 inv163
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2753_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 65, 36, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2753_orbit
  simpa only [lower10] using h

theorem space2754_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 145, 80, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 138), (145, 387), (80, 373), (48, 8), (9, 360), (4, 128), (3, 384)]
    (codeMat 87) (codeMat 115) (codeMat 492) false
    det87 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2754_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 145, 80, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2754_orbit
  simpa only [lower14] using h

theorem space2755_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 128, 80, 32, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 277), (128, 360), (80, 413), (32, 130), (9, 3), (4, 128), (3, 384)]
    (codeMat 107) (codeMat 171) (codeMat 485) false
    det107 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2755_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 128, 80, 32, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2755_orbit
  simpa only [lower14] using h

theorem space2756_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 144, 80, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (144, 325), (80, 326), (33, 176), (9, 432), (4, 16), (3, 24)]
    (codeMat 140) (codeMat 234) (codeMat 461) false
    det140 det234 inv234
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2756_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 80, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2756_orbit
  simpa only [lower10] using h

theorem space2757_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 81, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 503), (128, 325), (81, 246), (49, 176), (9, 432), (5, 8), (3, 24)]
    (codeMat 142) (codeMat 494) (codeMat 501) false
    det142 det494 inv494
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2757_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 81, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2757_orbit
  simpa only [lower10] using h

theorem space2758_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 128, 81, 32, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 68), (128, 325), (81, 246), (32, 256), (9, 432), (5, 16), (3, 24)]
    (codeMat 142) (codeMat 458) (codeMat 458) false
    det142 det458 inv458
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2758_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 128, 81, 32, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2758_orbit
  simpa only [lower10] using h

theorem space2759_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 20), (131, 30), (65, 3), (35, 264), (18, 384), (10, 232), (7, 8)]
    (codeMat 205) (codeMat 409) (codeMat 473) false
    det205 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2759_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space2759_orbit
  simpa only [lower14] using h

theorem space2760_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 65, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 327), (129, 326), (65, 325), (34, 440), (18, 432), (10, 424), (7, 256)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    det84 det501 inv501
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2760_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2760_orbit
  simpa only [lower10] using h

theorem space2761_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 33, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 508), (130, 2), (67, 148), (33, 373), (16, 130), (10, 276), (7, 511)]
    (codeMat 477) (codeMat 124) (codeMat 124) false
    det477 det124 inv124
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2761_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 33, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space2761_orbit
  simpa only [lower14] using h

theorem space2762_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 67, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 2), (67, 327), (32, 8), (16, 16), (10, 184), (7, 256)]
    (codeMat 84) (codeMat 93) (codeMat 372) false
    det84 det93 inv93
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2762_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2762_orbit
  simpa only [lower10] using h

theorem space2763_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 129), (130, 1), (64, 384), (35, 284), (18, 8), (10, 503), (6, 130)]
    (codeMat 285) (codeMat 110) (codeMat 444) false
    det285 det110 inv110
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2763_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space2763_orbit
  simpa only [lower14] using h

theorem space2764_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 67, 33, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (129, 414), (67, 373), (33, 23), (17, 30), (10, 29), (6, 8)]
    (codeMat 395) (codeMat 501) (codeMat 494) false
    det395 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2764_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 67, 33, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space2764_orbit
  simpa only [lower14] using h

theorem space2765_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 67, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 130), (129, 414), (67, 235), (33, 136), (18, 384), (10, 232), (5, 8)]
    (codeMat 207) (codeMat 185) (codeMat 481) false
    det207 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2765_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 67, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space2765_orbit
  simpa only [lower14] using h

theorem space2766_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 66, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 68), (128, 1), (66, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    det92 det331 inv331
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2766_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space2766_orbit
  simpa only [lower10] using h

theorem space2767_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 2), (66, 21), (33, 97), (18, 130), (10, 381), (4, 8)]
    (codeMat 460) (codeMat 85) (codeMat 340) false
    det460 det85 inv85
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2767_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space2767_orbit
  simpa only [lower14] using h

theorem space2768_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 65, 35, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 210), (130, 54), (65, 63), (35, 208), (17, 112), (10, 120), (4, 128)]
    (codeMat 94) (codeMat 249) (codeMat 425) false
    det94 det249 inv249
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2768_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 35, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2768_orbit
  simpa only [lower11] using h

theorem space2769_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 64, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (133, 224), (64, 128), (37, 406), (20, 235), (9, 130), (3, 8)]
    (codeMat 271) (codeMat 314) (codeMat 271) false
    det271 det314 inv314
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2769_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2769_orbit
  simpa only [lower14] using h

theorem space2770_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 145, 81, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 501), (145, 503), (81, 502), (49, 176), (9, 432), (5, 24), (3, 8)]
    (codeMat 140) (codeMat 478) (codeMat 445) false
    det140 det478 inv478
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2770_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2770_orbit
  simpa only [lower10] using h

theorem space2771_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 65, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 88), (65, 216), (32, 54), (16, 63), (9, 3), (5, 40), (3, 32)]
    (codeMat 267) (codeMat 443) (codeMat 254) false
    det267 det443 inv443
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2771_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 65, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2771_orbit
  simpa only [lower11] using h

theorem space2772_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 129, 80, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 28), (129, 383), (80, 21), (33, 352), (9, 360), (4, 256), (3, 128)]
    (codeMat 86) (codeMat 467) (codeMat 339) false
    det86 det467 inv467
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2772_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 129, 80, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2772_orbit
  simpa only [lower14] using h

theorem space2773_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 129, 64, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 60), (129, 138), (64, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 143) (codeMat 281) (codeMat 281) false
    det143 det281 inv281
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2773_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 129, 64, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2773_orbit
  simpa only [lower11] using h

theorem space2774_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [385, 64, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(385, 208), (64, 128), (33, 52), (16, 63), (9, 2), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 410) (codeMat 331) false
    det267 det410 inv410
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2774_lower : 12 ≤ frozenWangTable.L0 (spanCodes [385, 64, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2774_orbit
  simpa only [lower11] using h

theorem space2775_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 139), (132, 245), (65, 130), (37, 136), (21, 264), (8, 128), (2, 360)]
    (codeMat 159) (codeMat 174) (codeMat 359) false
    det159 det174 inv174
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2775_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2775_orbit
  simpa only [lower14] using h

theorem space2776_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 3), (129, 509), (65, 2), (37, 136), (21, 264), (8, 128), (2, 360)]
    (codeMat 157) (codeMat 174) (codeMat 359) false
    det157 det174 inv174
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2776_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2776_orbit
  simpa only [lower14] using h

theorem space2777_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 65, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (132, 324), (65, 3), (32, 8), (21, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    det85 det141 inv141
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2777_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2777_orbit
  simpa only [lower10] using h

theorem space2778_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (129, 246), (81, 413), (49, 264), (8, 360), (5, 128), (2, 384)]
    (codeMat 94) (codeMat 501) (codeMat 494) false
    det94 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2778_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2778_orbit
  simpa only [lower14] using h

theorem space2779_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 128, 81, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 230), (128, 3), (81, 228), (33, 416), (8, 256), (5, 16), (2, 24)]
    (codeMat 140) (codeMat 370) (codeMat 207) false
    det140 det370 inv370
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2779_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 128, 81, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2779_orbit
  simpa only [lower10] using h

theorem space2780_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (128, 1), (80, 68), (49, 160), (8, 256), (4, 24), (2, 8)]
    (codeMat 140) (codeMat 102) (codeMat 156) false
    det140 det102 inv102
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2780_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2780_orbit
  simpa only [lower10] using h

theorem space2781_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 144, 80, 33, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (144, 8), (80, 264), (33, 149), (8, 360), (4, 2), (2, 1)]
    (codeMat 305) (codeMat 99) (codeMat 172) false
    det305 det99 inv99
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2781_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 80, 33, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2781_orbit
  simpa only [lower14] using h

theorem space2782_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 34, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (130, 360), (66, 104), (34, 414), (22, 373), (10, 97), (1, 8)]
    (codeMat 271) (codeMat 419) (codeMat 183) false
    det271 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2782_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2782_orbit
  simpa only [lower14] using h

theorem space2783_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 130, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 3), (130, 1), (70, 509), (34, 136), (18, 8), (10, 264), (1, 360)]
    (codeMat 157) (codeMat 103) (codeMat 188) false
    det157 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2783_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2783_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
