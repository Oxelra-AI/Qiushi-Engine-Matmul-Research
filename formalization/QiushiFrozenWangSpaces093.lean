import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2976_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 146, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 127), (146, 128), (96, 28), (10, 96), (4, 9), (1, 8)]
    (codeMat 185) (codeMat 172) (codeMat 99) true
    det185 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2976_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2976_orbit
  simpa only [lower35] using h

theorem space2977_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 96, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (128, 1), (96, 28), (16, 8), (10, 96), (6, 128)]
    (codeMat 84) (codeMat 102) (codeMat 156) false
    det84 det102 inv102
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2977_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 96, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space2977_orbit
  simpa only [lower35] using h

theorem space2978_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [291, 163, 96, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(291, 118), (163, 244), (96, 245), (17, 96), (10, 104), (6, 128)]
    (codeMat 93) (codeMat 481) (codeMat 185) false
    det93 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2978_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 163, 96, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space2978_orbit
  simpa only [lower35] using h

theorem space2979_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [274, 128, 82, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(274, 132), (128, 2), (82, 135), (50, 164), (10, 173)]
    (codeMat 244) (codeMat 345) (codeMat 345) false
    det244 det345 inv345
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2979_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 128, 82, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2979_orbit
  simpa only [lower103] using h

theorem space2980_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 64, 32, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (134, 20), (64, 9), (32, 128), (10, 96), (1, 8)]
    (codeMat 141) (codeMat 161) (codeMat 161) false
    det141 det161 inv161
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2980_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 64, 32, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2980_orbit
  simpa only [lower35] using h

theorem space2981_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 129, 65, 33, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (129, 139), (65, 9), (33, 31), (10, 252), (4, 3)]
    (codeMat 165) (codeMat 157) (codeMat 486) true
    det165 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2981_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2981_orbit
  simpa only [lower35] using h

theorem space2982_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 144, 82, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 246), (144, 3), (82, 252), (50, 232), (10, 224), (5, 128)]
    (codeMat 86) (codeMat 370) (codeMat 207) false
    det86 det370 inv370
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2982_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 82, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2982_orbit
  simpa only [lower35] using h

theorem space2983_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 65, 33, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 128), (65, 8), (33, 28), (10, 224), (4, 3)]
    (codeMat 165) (codeMat 140) (codeMat 98) true
    det165 det140 inv140
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2983_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2983_orbit
  simpa only [lower35] using h

theorem space2984_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 130, 81, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 84), (130, 1), (81, 79), (49, 336), (10, 496), (7, 16)]
    (codeMat 205) (codeMat 331) (codeMat 410) false
    det205 det331 inv331
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2984_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 130, 81, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space2984_orbit
  simpa only [lower65] using h

theorem space2985_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 160, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (160, 148), (96, 20), (10, 104), (4, 1), (1, 8)]
    (codeMat 161) (codeMat 156) (codeMat 102) true
    det161 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2985_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2985_orbit
  simpa only [lower35] using h

theorem space2986_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [402, 80, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(402, 119), (80, 224), (48, 8), (10, 31), (6, 1), (1, 3)]
    (codeMat 401) (codeMat 443) (codeMat 254) false
    det401 det443 inv443
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2986_lower : 15 ≤ frozenWangTable.L0 (spanCodes [402, 80, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2986_orbit
  simpa only [lower35] using h

theorem space2987_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [257, 147, 80, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(257, 357), (147, 31), (80, 30), (48, 432), (10, 20), (4, 260)]
    (codeMat 93) (codeMat 286) (codeMat 303) true
    det93 det286 inv286
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space2987_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 147, 80, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 80 space2987_orbit
  simpa only [lower80] using h

theorem space2988_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 131, 65, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 10), (131, 30), (65, 3), (33, 136), (10, 232), (5, 8)]
    (codeMat 205) (codeMat 185) (codeMat 481) false
    det205 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2988_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2988_orbit
  simpa only [lower35] using h

theorem space2989_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [277, 144, 65, 33, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(277, 116), (144, 130), (65, 9), (33, 96), (8, 8), (2, 128)]
    (codeMat 87) (codeMat 273) (codeMat 273) false
    det87 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2989_lower : 15 ≤ frozenWangTable.L0 (spanCodes [277, 144, 65, 33, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2989_orbit
  simpa only [lower35] using h

theorem space2990_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [401, 80, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(401, 117), (80, 97), (48, 9), (8, 8), (5, 128), (2, 130)]
    (codeMat 266) (codeMat 426) (codeMat 335) true
    det266 det426 inv426
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2990_lower : 15 ≤ frozenWangTable.L0 (spanCodes [401, 80, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2990_orbit
  simpa only [lower35] using h

theorem space2991_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [274, 146, 71, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(274, 37), (146, 1), (71, 228), (39, 414), (10, 398)]
    (codeMat 351) (codeMat 335) (codeMat 426) false
    det351 det335 inv335
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space2991_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 146, 71, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space2991_orbit
  simpa only [lower220] using h

theorem space2992_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [272, 145, 64, 32, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(272, 186), (145, 255), (64, 260), (32, 16), (10, 480), (6, 320)]
    (codeMat 85) (codeMat 242) (codeMat 205) false
    det85 det242 inv242
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space2992_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 145, 64, 32, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space2992_orbit
  simpa only [lower65] using h

theorem space2993_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [400, 80, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(400, 104), (80, 232), (48, 8), (10, 29), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 395) (codeMat 474) false
    det273 det395 inv395
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2993_lower : 15 ≤ frozenWangTable.L0 (spanCodes [400, 80, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2993_orbit
  simpa only [lower35] using h

theorem space2994_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 162, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (162, 148), (96, 28), (10, 104), (4, 1), (1, 8)]
    (codeMat 169) (codeMat 156) (codeMat 102) true
    det169 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2994_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 162, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2994_orbit
  simpa only [lower35] using h

theorem space2995_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 144, 80, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 10), (144, 2), (80, 34), (48, 9), (10, 164)]
    (codeMat 230) (codeMat 124) (codeMat 124) false
    det230 det124 inv124
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2995_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 144, 80, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2995_orbit
  simpa only [lower103] using h

theorem space2996_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [288, 128, 96, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(288, 2), (128, 8), (96, 34), (16, 9), (10, 118)]
    (codeMat 102) (codeMat 106) (codeMat 396) false
    det102 det106 inv106
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2996_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 96, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 101 space2996_orbit
  simpa only [lower101] using h

theorem space2997_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [384, 64, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(384, 8), (64, 32), (32, 3), (16, 2), (10, 132)]
    (codeMat 98) (codeMat 116) (codeMat 92) false
    det98 det116 inv116
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2997_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 64, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2997_orbit
  simpa only [lower103] using h

theorem space2998_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 64, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 22), (134, 20), (64, 128), (32, 9), (16, 8), (10, 96)]
    (codeMat 98) (codeMat 116) (codeMat 92) true
    det98 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2998_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2998_orbit
  simpa only [lower35] using h

theorem space2999_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [386, 66, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(386, 164), (66, 173), (34, 134), (16, 2), (10, 133)]
    (codeMat 114) (codeMat 369) (codeMat 377) false
    det114 det369 inv369
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2999_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 66, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2999_orbit
  simpa only [lower103] using h

theorem space3000_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 135, 66, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 252), (135, 28), (66, 227), (34, 104), (16, 8), (10, 97)]
    (codeMat 114) (codeMat 369) (codeMat 377) true
    det114 det369 inv369
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3000_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 66, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3000_orbit
  simpa only [lower35] using h

theorem space3001_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (130, 130), (71, 150), (39, 96), (17, 97), (10, 105)]
    (codeMat 107) (codeMat 459) (codeMat 346) true
    det107 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3001_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3001_orbit
  simpa only [lower35] using h

theorem space3002_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [258, 132, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(258, 68), (132, 69), (71, 71), (39, 160), (17, 168), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    det93 det459 inv459
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space3002_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space3002_orbit
  simpa only [lower29] using h

theorem space3003_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 232), (135, 224), (71, 96), (39, 150), (17, 151), (10, 149)]
    (codeMat 299) (codeMat 499) (codeMat 382) false
    det299 det499 inv499
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3003_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3003_orbit
  simpa only [lower35] using h

theorem space3004_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    det212 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3004_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3004_orbit
  simpa only [lower35] using h

theorem space3005_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 70, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 20), (134, 22), (70, 148), (38, 28), (22, 31), (10, 252)]
    (codeMat 102) (codeMat 122) (codeMat 460) true
    det102 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3005_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 70, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3005_orbit
  simpa only [lower35] using h

theorem space3006_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 65, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 148), (132, 150), (65, 130), (33, 252), (23, 255), (10, 227)]
    (codeMat 110) (codeMat 499) (codeMat 382) true
    det110 det499 inv499
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3006_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 65, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3006_orbit
  simpa only [lower35] using h

theorem space3007_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 135, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (135, 104), (71, 105), (39, 22), (17, 148), (10, 150)]
    (codeMat 92) (codeMat 253) (codeMat 415) true
    det92 det253 inv253
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3007_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3007_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
