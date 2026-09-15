import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2560_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 65, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (134, 148), (65, 128), (36, 3), (21, 252), (10, 224)]
    (codeMat 110) (codeMat 212) (codeMat 86) true
    det110 det212 inv212
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2560_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 65, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2560_orbit
  simpa only [lower35] using h

theorem space2561_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 133, 64, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 496), (133, 160), (64, 320), (32, 1), (20, 78), (10, 437)]
    (codeMat 298) (codeMat 213) (codeMat 470) false
    det298 det213 inv213
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2561_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 64, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2561_orbit
  simpa only [lower65] using h

theorem space2562_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [288, 132, 66, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(288, 128), (132, 246), (66, 29), (22, 255), (10, 31), (1, 3)]
    (codeMat 183) (codeMat 275) (codeMat 275) true
    det183 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2562_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 132, 66, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2562_orbit
  simpa only [lower35] using h

theorem space2563_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [276, 146, 84, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(276, 133), (146, 325), (84, 165), (50, 367), (10, 366)]
    (codeMat 354) (codeMat 234) (codeMat 461) false
    det354 det234 inv234
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space2563_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 146, 84, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 197 space2563_orbit
  simpa only [lower197] using h

theorem space2564_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [288, 129, 65, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(288, 32), (129, 129), (65, 1), (21, 413), (10, 139)]
    (codeMat 309) (codeMat 275) (codeMat 275) false
    det309 det275 inv275
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space2564_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 129, 65, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 189 space2564_orbit
  simpa only [lower189] using h

theorem space2565_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [261, 128, 65, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(261, 366), (128, 1), (65, 432), (36, 192), (21, 356), (10, 127)]
    (codeMat 244) (codeMat 110) (codeMat 444) false
    det244 det110 inv110
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space2565_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space2565_orbit
  simpa only [lower80] using h

theorem space2566_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 135, 65, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (135, 20), (65, 130), (34, 224), (21, 28), (10, 227)]
    (codeMat 111) (codeMat 337) (codeMat 337) true
    det111 det337 inv337
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2566_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 65, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2566_orbit
  simpa only [lower35] using h

theorem space2567_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 134, 67, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 320), (134, 336), (67, 480), (37, 437), (23, 79), (10, 507)]
    (codeMat 298) (codeMat 415) (codeMat 253) false
    det298 det415 inv415
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2567_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 67, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2567_orbit
  simpa only [lower65] using h

theorem space2568_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 131, 67, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 480), (131, 160), (67, 176), (37, 507), (23, 78), (10, 436)]
    (codeMat 354) (codeMat 244) (codeMat 95) false
    det354 det244 inv244
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2568_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 67, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2568_orbit
  simpa only [lower65] using h

theorem space2569_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 36, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    det212 det98 inv98
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2569_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2569_orbit
  simpa only [lower35] using h

theorem space2570_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 130, 68, 39, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 150), (130, 1), (68, 148), (39, 232), (16, 8), (10, 104)]
    (codeMat 213) (codeMat 354) (codeMat 142) false
    det213 det354 inv354
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2570_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 68, 39, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2570_orbit
  simpa only [lower35] using h

theorem space2571_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 133, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 8), (133, 232), (69, 104), (36, 1), (17, 150), (10, 148)]
    (codeMat 299) (codeMat 212) (codeMat 86) false
    det299 det212 inv212
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2571_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2571_orbit
  simpa only [lower35] using h

theorem space2572_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 8), (134, 104), (69, 105), (39, 20), (17, 148), (10, 150)]
    (codeMat 93) (codeMat 249) (codeMat 425) true
    det93 det249 inv249
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2572_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2572_orbit
  simpa only [lower35] using h

theorem space2573_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 80, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 3), (80, 28), (48, 8), (10, 224), (4, 128)]
    (codeMat 84) (codeMat 114) (codeMat 204) false
    det84 det114 inv114
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2573_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 80, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2573_orbit
  simpa only [lower35] using h

theorem space2574_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [257, 147, 80, 34, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(257, 462), (147, 30), (80, 31), (34, 272), (10, 20), (4, 432)]
    (codeMat 157) (codeMat 313) (codeMat 313) true
    det157 det313 inv313
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space2574_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 147, 80, 34, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 80 space2574_orbit
  simpa only [lower80] using h

theorem space2575_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 145, 81, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 507), (145, 447), (81, 446), (50, 480), (10, 496), (5, 320)]
    (codeMat 84) (codeMat 254) (codeMat 443) false
    det84 det254 inv254
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2575_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 145, 81, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space2575_orbit
  simpa only [lower65] using h

theorem space2576_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 146, 82, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 270), (146, 260), (82, 276), (49, 78), (10, 436), (6, 1)]
    (codeMat 417) (codeMat 460) (codeMat 122) false
    det417 det460 inv460
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2576_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 146, 82, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2576_orbit
  simpa only [lower65] using h

theorem space2577_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 144, 82, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 171), (144, 1), (82, 447), (51, 160), (10, 496), (6, 16)]
    (codeMat 206) (codeMat 111) (codeMat 412) false
    det206 det111 inv111
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2577_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 144, 82, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2577_orbit
  simpa only [lower65] using h

theorem space2578_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 144, 82, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 228), (144, 1), (82, 446), (33, 160), (10, 496), (6, 320)]
    (codeMat 94) (codeMat 330) (codeMat 394) false
    det94 det330 inv330
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2578_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 144, 82, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2578_orbit
  simpa only [lower65] using h

theorem space2579_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 135, 67, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 320), (135, 176), (67, 480), (33, 437), (23, 436), (10, 507)]
    (codeMat 355) (codeMat 397) (codeMat 250) false
    det355 det397 inv397
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2579_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 67, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2579_orbit
  simpa only [lower65] using h

theorem space2580_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 130, 67, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 480), (130, 16), (67, 176), (33, 507), (23, 506), (10, 436)]
    (codeMat 299) (codeMat 116) (codeMat 92) false
    det299 det116 inv116
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2580_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2580_orbit
  simpa only [lower65] using h

theorem space2581_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 132, 67, 34, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (132, 287), (67, 497), (34, 480), (23, 336), (10, 496)]
    (codeMat 215) (codeMat 183) (codeMat 419) false
    det215 det183 inv183
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2581_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 67, 34, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space2581_orbit
  simpa only [lower65] using h

theorem space2582_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 128, 66, 39, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 1), (128, 256), (66, 452), (39, 463), (22, 97), (10, 479)]
    (codeMat 285) (codeMat 141) (codeMat 226) false
    det285 det141 inv141
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space2582_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 66, 39, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space2582_orbit
  simpa only [lower69] using h

theorem space2583_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 129, 66, 34, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 1), (129, 196), (66, 452), (34, 463), (22, 446), (10, 479)]
    (codeMat 340) (codeMat 159) (codeMat 230) false
    det340 det159 inv159
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space2583_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 34, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space2583_orbit
  simpa only [lower69] using h

theorem space2584_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 133, 69, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 96), (133, 105), (69, 104), (36, 128), (17, 150), (10, 148)]
    (codeMat 92) (codeMat 474) (codeMat 395) true
    det92 det474 inv474
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2584_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2584_orbit
  simpa only [lower35] using h

theorem space2585_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 134, 69, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 104), (134, 224), (69, 96), (39, 148), (17, 151), (10, 149)]
    (codeMat 355) (codeMat 467) (codeMat 339) false
    det355 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2585_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 134, 69, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2585_orbit
  simpa only [lower35] using h

theorem space2586_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 130, 81, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 85), (130, 1), (81, 79), (33, 336), (10, 496), (5, 16)]
    (codeMat 205) (codeMat 335) (codeMat 426) false
    det205 det335 inv335
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2586_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 81, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space2586_orbit
  simpa only [lower65] using h

theorem space2587_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [272, 128, 81, 32, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(272, 69), (128, 260), (81, 255), (32, 320), (10, 480), (5, 16)]
    (codeMat 142) (codeMat 461) (codeMat 234) false
    det142 det461 inv461
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2587_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 128, 81, 32, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space2587_orbit
  simpa only [lower65] using h

theorem space2588_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 160, 65, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 1), (160, 10), (65, 260), (16, 16), (10, 160), (5, 320)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2588_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 65, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space2588_orbit
  simpa only [lower65] using h

theorem space2589_orbit :
    frozenWangTable.OrbitImage 76 (spanCodes [274, 131, 83, 35, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 76 [(274, 11), (131, 378), (83, 453), (35, 289), (10, 367), (7, 288)]
    (codeMat 443) (codeMat 93) (codeMat 372) false
    det443 det93 inv93
    (by rw [basis76]; decide +kernel)
    (by rw [basis76]; decide +kernel)

theorem space2589_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 131, 83, 35, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 76 space2589_orbit
  simpa only [lower76] using h

theorem space2590_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 131, 82, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 276), (131, 446), (82, 79), (50, 176), (10, 496), (6, 16)]
    (codeMat 143) (codeMat 473) (codeMat 409) false
    det143 det473 inv473
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2590_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 82, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2590_orbit
  simpa only [lower65] using h

theorem space2591_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [292, 134, 66, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(292, 128), (134, 246), (66, 30), (22, 255), (10, 31), (1, 3)]
    (codeMat 190) (codeMat 275) (codeMat 275) true
    det190 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2591_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 134, 66, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2591_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
