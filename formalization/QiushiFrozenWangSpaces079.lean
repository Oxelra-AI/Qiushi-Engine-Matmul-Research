import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2528_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 130, 83, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 254), (130, 27), (83, 255), (49, 336), (10, 480), (7, 16)]
    (codeMat 204) (codeMat 379) (codeMat 247) false
    det204 det379 inv379
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2528_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 83, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2528_orbit
  simpa only [lower65] using h

theorem space2529_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 144, 83, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 1), (144, 260), (83, 287), (48, 320), (10, 480), (7, 16)]
    (codeMat 140) (codeMat 205) (codeMat 242) false
    det140 det205 inv205
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2529_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 144, 83, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2529_orbit
  simpa only [lower65] using h

theorem space2530_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [401, 80, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(401, 234), (80, 252), (49, 10), (9, 9), (4, 128), (3, 130)]
    (codeMat 267) (codeMat 409) (codeMat 473) true
    det267 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2530_lower : 15 ≤ frozenWangTable.L0 (spanCodes [401, 80, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2530_orbit
  simpa only [lower35] using h

theorem space2531_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [400, 81, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(400, 96), (81, 118), (48, 8), (8, 9), (5, 130), (2, 128)]
    (codeMat 266) (codeMat 425) (codeMat 249) true
    det266 det425 inv425
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2531_lower : 15 ≤ frozenWangTable.L0 (spanCodes [400, 81, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2531_orbit
  simpa only [lower35] using h

theorem space2532_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [400, 82, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(400, 96), (82, 245), (48, 8), (10, 29), (6, 1), (1, 3)]
    (codeMat 401) (codeMat 395) (codeMat 474) false
    det401 det395 inv395
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2532_lower : 15 ≤ frozenWangTable.L0 (spanCodes [400, 82, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2532_orbit
  simpa only [lower35] using h

theorem space2533_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [295, 131, 64, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(295, 170), (131, 129), (64, 1), (20, 413), (10, 139)]
    (codeMat 380) (codeMat 279) (codeMat 279) false
    det380 det279 inv279
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space2533_lower : 15 ≤ frozenWangTable.L0 (spanCodes [295, 131, 64, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 189 space2533_orbit
  simpa only [lower189] using h

theorem space2534_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 128, 65, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 245), (128, 260), (65, 27), (32, 320), (21, 176), (10, 480)]
    (codeMat 158) (codeMat 397) (codeMat 250) false
    det158 det397 inv397
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2534_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2534_orbit
  simpa only [lower65] using h

theorem space2535_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 131, 65, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 437), (131, 78), (65, 1), (32, 320), (21, 160), (10, 496)]
    (codeMat 157) (codeMat 405) (codeMat 407) false
    det157 det405 inv405
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2535_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 131, 65, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2535_orbit
  simpa only [lower65] using h

theorem space2536_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 129, 65, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 480), (129, 336), (65, 16), (34, 507), (21, 79), (10, 506)]
    (codeMat 298) (codeMat 190) (codeMat 355) false
    det298 det190 inv190
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2536_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 129, 65, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2536_orbit
  simpa only [lower65] using h

theorem space2537_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 129, 66, 35, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 9), (129, 104), (66, 96), (35, 31), (22, 252), (10, 224)]
    (codeMat 117) (codeMat 244) (codeMat 95) true
    det117 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2537_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 66, 35, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2537_orbit
  simpa only [lower35] using h

theorem space2538_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 66, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (128, 8), (66, 96), (38, 31), (22, 28), (10, 224)]
    (codeMat 116) (codeMat 116) (codeMat 92) true
    det116 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2538_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2538_orbit
  simpa only [lower35] using h

theorem space2539_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 133, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 224), (133, 28), (68, 255), (34, 96), (16, 8), (10, 105)]
    (codeMat 122) (codeMat 345) (codeMat 345) true
    det122 det345 inv345
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2539_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2539_orbit
  simpa only [lower35] using h

theorem space2540_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 68, 37, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 126), (130, 9), (68, 245), (37, 232), (16, 8), (10, 96)]
    (codeMat 215) (codeMat 355) (codeMat 190) false
    det215 det355 inv355
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2540_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 68, 37, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2540_orbit
  simpa only [lower35] using h

theorem space2541_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 134, 68, 38, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 79), (134, 506), (68, 78), (38, 336), (16, 16), (10, 160)]
    (codeMat 213) (codeMat 380) (codeMat 117) false
    det213 det380 inv380
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2541_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 68, 38, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2541_orbit
  simpa only [lower65] using h

theorem space2542_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 135, 70, 35, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 436), (135, 437), (70, 79), (35, 176), (18, 320), (10, 336)]
    (codeMat 212) (codeMat 459) (codeMat 346) false
    det212 det459 inv459
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2542_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 70, 35, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2542_orbit
  simpa only [lower65] using h

theorem space2543_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 135, 65, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 496), (135, 480), (65, 320), (36, 1), (21, 507), (10, 437)]
    (codeMat 355) (codeMat 87) (codeMat 468) false
    det355 det87 inv87
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2543_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 65, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2543_orbit
  simpa only [lower65] using h

theorem space2544_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 133, 66, 32, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 506), (133, 79), (66, 507), (32, 16), (22, 336), (10, 480)]
    (codeMat 212) (codeMat 187) (codeMat 229) false
    det212 det187 inv187
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2544_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 66, 32, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2544_orbit
  simpa only [lower65] using h

theorem space2545_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [290, 132, 66, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(290, 136), (132, 232), (66, 30), (22, 224), (10, 28), (1, 3)]
    (codeMat 183) (codeMat 305) (codeMat 305) true
    det183 det305 inv305
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2545_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 132, 66, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2545_orbit
  simpa only [lower35] using h

theorem space2546_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 132, 70, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 507), (132, 437), (70, 79), (33, 480), (18, 320), (10, 336)]
    (codeMat 213) (codeMat 239) (codeMat 351) false
    det213 det239 inv239
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2546_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 132, 70, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2546_orbit
  simpa only [lower65] using h

theorem space2547_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 129, 70, 38, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 238), (129, 490), (70, 287), (38, 160), (18, 16), (10, 336)]
    (codeMat 159) (codeMat 377) (codeMat 369) false
    det159 det377 inv377
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2547_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 70, 38, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2547_orbit
  simpa only [lower65] using h

theorem space2548_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (128, 1), (68, 104), (34, 20), (16, 2), (10, 148)]
    (codeMat 84) (codeMat 106) (codeMat 396) true
    det84 det106 inv106
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2548_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2548_orbit
  simpa only [lower35] using h

theorem space2549_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 130, 64, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 480), (130, 320), (64, 16), (39, 507), (20, 437), (10, 506)]
    (codeMat 355) (codeMat 174) (codeMat 359) false
    det355 det174 inv174
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2549_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2549_orbit
  simpa only [lower65] using h

theorem space2550_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 131, 64, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 245), (131, 287), (64, 27), (36, 320), (20, 336), (10, 480)]
    (codeMat 214) (codeMat 415) (codeMat 253) false
    det214 det415 inv415
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2550_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2550_orbit
  simpa only [lower65] using h

theorem space2551_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [289, 133, 65, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(289, 20), (133, 235), (65, 130), (21, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 282) (codeMat 267) false
    det206 det282 inv282
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2551_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 133, 65, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2551_orbit
  simpa only [lower35] using h

theorem space2552_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [259, 133, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(259, 269), (133, 139), (84, 396), (53, 294), (10, 295)]
    (codeMat 443) (codeMat 351) (codeMat 239) false
    det443 det351 inv351
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space2552_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space2552_orbit
  simpa only [lower187] using h

theorem space2553_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [259, 151, 84, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(259, 160), (151, 139), (84, 171), (39, 294), (10, 295)]
    (codeMat 299) (codeMat 379) (codeMat 247) false
    det299 det379 inv379
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space2553_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 151, 84, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space2553_orbit
  simpa only [lower187] using h

theorem space2554_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 133, 69, 34, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 150), (133, 149), (69, 148), (34, 232), (17, 96), (10, 104)]
    (codeMat 156) (codeMat 482) (codeMat 143) false
    det156 det482 inv482
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2554_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 34, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2554_orbit
  simpa only [lower35] using h

theorem space2555_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 69, 32, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (134, 148), (69, 149), (32, 128), (17, 104), (10, 96)]
    (codeMat 157) (codeMat 225) (codeMat 169) false
    det157 det225 inv225
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2555_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 69, 32, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2555_orbit
  simpa only [lower35] using h

theorem space2556_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 148), (128, 130), (69, 150), (39, 104), (17, 97), (10, 105)]
    (codeMat 99) (codeMat 491) (codeMat 375) true
    det99 det491 inv491
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2556_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2556_orbit
  simpa only [lower35] using h

theorem space2557_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (130, 128), (69, 148), (36, 1), (17, 96), (10, 104)]
    (codeMat 107) (codeMat 204) (codeMat 114) true
    det107 det204 inv204
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2557_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2557_orbit
  simpa only [lower35] using h

theorem space2558_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [260, 128, 66, 33, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(260, 260), (128, 432), (66, 272), (33, 453), (22, 378), (10, 464)]
    (codeMat 335) (codeMat 468) (codeMat 87) true
    det335 det468 inv468
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space2558_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 66, 33, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space2558_orbit
  simpa only [lower80] using h

theorem space2559_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 135, 66, 32, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 490), (135, 287), (66, 497), (32, 16), (22, 336), (10, 496)]
    (codeMat 214) (codeMat 179) (codeMat 421) false
    det214 det179 inv179
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2559_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 32, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2559_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
