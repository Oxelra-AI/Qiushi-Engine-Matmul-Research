import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2656_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 64, 35, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 274), (131, 228), (64, 63), (35, 208), (16, 32), (10, 312), (4, 128)]
    (codeMat 86) (codeMat 233) (codeMat 233) false
    det86 det233 inv233
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2656_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 35, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space2656_orbit
  simpa only [lower17] using h

theorem space2657_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 131, 65, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 390), (131, 69), (65, 1), (33, 112), (18, 360), (10, 328), (7, 128)]
    (codeMat 85) (codeMat 419) (codeMat 183) false
    det85 det419 inv419
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2657_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space2657_orbit
  simpa only [lower17] using h

theorem space2658_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 65, 35, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 329), (131, 429), (65, 219), (35, 456), (16, 360), (10, 408), (5, 128)]
    (codeMat 95) (codeMat 143) (codeMat 482) false
    det95 det143 inv143
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2658_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 35, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space2658_orbit
  simpa only [lower17] using h

theorem space2659_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 131, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 274), (131, 301), (66, 329), (33, 80), (18, 360), (10, 328), (4, 128)]
    (codeMat 86) (codeMat 163) (codeMat 165) false
    det86 det163 inv163
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2659_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space2659_orbit
  simpa only [lower17] using h

theorem space2660_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 33, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 274), (129, 429), (64, 219), (33, 80), (16, 360), (10, 408), (4, 128)]
    (codeMat 94) (codeMat 171) (codeMat 485) false
    det94 det171 inv171
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space2660_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 33, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space2660_orbit
  simpa only [lower17] using h

theorem space2661_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [64, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(64, 4), (36, 216), (20, 208), (8, 1), (2, 128), (1, 2)]
    (codeMat 266) (codeMat 417) (codeMat 177) true
    det266 det417 inv417
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space2661_lower : 12 ≤ frozenWangTable.L0 (spanCodes [64, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space2661_orbit
  simpa only [lower23] using h

theorem space2662_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [129, 64, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(129, 80), (64, 128), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2662_lower : 12 ≤ frozenWangTable.L0 (spanCodes [129, 64, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2662_orbit
  simpa only [lower11] using h

theorem space2663_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [129, 64, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(129, 208), (64, 128), (32, 54), (17, 11), (9, 2), (5, 32), (3, 8)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    det267 det314 inv314
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2663_lower : 12 ≤ frozenWangTable.L0 (spanCodes [129, 64, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2663_orbit
  simpa only [lower11] using h

theorem space2664_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [128, 65, 33, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(128, 128), (65, 216), (33, 60), (17, 10), (9, 3), (4, 32), (3, 8)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    det267 det281 inv281
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2664_lower : 12 ≤ frozenWangTable.L0 (spanCodes [128, 65, 33, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2664_orbit
  simpa only [lower11] using h

theorem space2665_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [129, 65, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(129, 88), (65, 216), (33, 30), (16, 1), (8, 3), (5, 40), (2, 8)]
    (codeMat 266) (codeMat 299) (codeMat 318) false
    det266 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2665_lower : 12 ≤ frozenWangTable.L0 (spanCodes [129, 65, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2665_orbit
  simpa only [lower11] using h

theorem space2666_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 64, 34, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 196), (64, 128), (34, 28), (16, 32), (10, 20), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 172) (codeMat 99) false
    det273 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2666_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2666_orbit
  simpa only [lower11] using h

theorem space2667_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 66, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 70), (66, 198), (32, 8), (18, 54), (10, 30), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 157) (codeMat 486) false
    det273 det157 inv157
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2667_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 66, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2667_orbit
  simpa only [lower11] using h

theorem space2668_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 66, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (66, 198), (34, 22), (18, 54), (10, 30), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 185) (codeMat 481) false
    det273 det185 inv185
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2668_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 66, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2668_orbit
  simpa only [lower11] using h

theorem space2669_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 65, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 88), (65, 216), (32, 1), (17, 28), (8, 3), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 141) (codeMat 226) false
    det266 det141 inv141
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2669_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 65, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2669_orbit
  simpa only [lower11] using h

theorem space2670_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 65, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 52), (128, 9), (65, 2), (17, 80), (8, 128), (4, 32), (2, 8)]
    (codeMat 141) (codeMat 266) (codeMat 266) false
    det141 det266 inv266
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2670_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2670_orbit
  simpa only [lower11] using h

theorem space2671_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 65, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (129, 10), (65, 3), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 141) (codeMat 313) (codeMat 313) false
    det141 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2671_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2671_orbit
  simpa only [lower11] using h

theorem space2672_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (130, 3), (64, 9), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 141) (codeMat 307) (codeMat 311) false
    det141 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2672_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2672_orbit
  simpa only [lower11] using h

theorem space2673_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 30), (128, 3), (64, 1), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 140) (codeMat 307) (codeMat 311) false
    det140 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2673_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2673_orbit
  simpa only [lower11] using h

theorem space2674_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 20), (128, 2), (64, 1), (16, 128), (10, 80), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    det140 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2674_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2674_orbit
  simpa only [lower11] using h

theorem space2675_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [292, 160, 68, 16, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(292, 511), (160, 71), (68, 184), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2675_lower : 12 ≤ frozenWangTable.L0 (spanCodes [292, 160, 68, 16, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2675_orbit
  simpa only [lower10] using h

theorem space2676_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 144, 81, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 326), (144, 3), (81, 484), (33, 416), (8, 256), (5, 16), (2, 24)]
    (codeMat 142) (codeMat 370) (codeMat 207) false
    det142 det370 inv370
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2676_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 81, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2676_orbit
  simpa only [lower10] using h

theorem space2677_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 144, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (144, 3), (81, 484), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 142) (codeMat 342) (codeMat 215) false
    det142 det342 inv342
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2677_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2677_orbit
  simpa only [lower10] using h

theorem space2678_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 80, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 178), (129, 503), (80, 70), (33, 176), (9, 432), (4, 16), (3, 8)]
    (codeMat 142) (codeMat 250) (codeMat 397) false
    det142 det250 inv250
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2678_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 80, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2678_orbit
  simpa only [lower10] using h

theorem space2679_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 129, 80, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 259), (129, 503), (80, 70), (48, 256), (9, 432), (4, 24), (3, 8)]
    (codeMat 142) (codeMat 254) (codeMat 443) false
    det142 det254 inv254
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2679_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 129, 80, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2679_orbit
  simpa only [lower10] using h

theorem space2680_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 144, 80, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 31), (144, 384), (80, 392), (48, 360), (9, 511), (4, 3), (3, 1)]
    (codeMat 417) (codeMat 253) (codeMat 415) false
    det417 det253 inv253
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2680_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 80, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2680_orbit
  simpa only [lower14] using h

theorem space2681_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 144, 81, 32, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 264), (144, 256), (81, 287), (32, 360), (9, 511), (5, 2), (3, 3)]
    (codeMat 417) (codeMat 461) (codeMat 234) false
    det417 det461 inv461
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2681_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 81, 32, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2681_orbit
  simpa only [lower14] using h

theorem space2682_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 145, 81, 32, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 500), (145, 503), (81, 502), (32, 256), (9, 432), (5, 16), (3, 8)]
    (codeMat 140) (codeMat 474) (codeMat 395) false
    det140 det474 inv474
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2682_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 32, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2682_orbit
  simpa only [lower10] using h

theorem space2683_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 144, 81, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 383), (144, 3), (81, 373), (49, 352), (9, 360), (5, 128), (3, 384)]
    (codeMat 86) (codeMat 375) (codeMat 491) false
    det86 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2683_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 81, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space2683_orbit
  simpa only [lower14] using h

theorem space2684_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 144, 80, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (144, 325), (80, 326), (48, 256), (9, 432), (4, 8), (3, 24)]
    (codeMat 140) (codeMat 206) (codeMat 498) false
    det140 det206 inv206
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2684_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 80, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2684_orbit
  simpa only [lower10] using h

theorem space2685_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 128, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 229), (128, 3), (81, 228), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 140) (codeMat 342) (codeMat 215) false
    det140 det342 inv342
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2685_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 128, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2685_orbit
  simpa only [lower10] using h

theorem space2686_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (145, 29), (81, 413), (49, 509), (8, 360), (5, 1), (2, 3)]
    (codeMat 305) (codeMat 339) (codeMat 467) false
    det305 det339 inv339
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2686_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space2686_orbit
  simpa only [lower14] using h

theorem space2687_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 80, 33, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (128, 1), (80, 68), (33, 160), (8, 256), (4, 16), (2, 8)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    det140 det98 inv98
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2687_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 80, 33, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2687_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
