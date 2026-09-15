import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2944_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [96, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(96, 134), (16, 1), (8, 2), (5, 32), (2, 8)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    det266 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2944_lower : 15 ≤ frozenWangTable.L0 (spanCodes [96, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2944_orbit
  simpa only [lower103] using h

theorem space2945_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [81, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(81, 175), (49, 11), (9, 2), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 410) (codeMat 331) false
    det267 det410 inv410
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2945_lower : 15 ≤ frozenWangTable.L0 (spanCodes [81, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2945_orbit
  simpa only [lower103] using h

theorem space2946_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 175), (48, 9), (9, 2), (5, 32), (3, 40)]
    (codeMat 331) (codeMat 442) (codeMat 334) false
    det331 det442 inv442
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2946_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2946_orbit
  simpa only [lower103] using h

theorem space2947_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [69, 37, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(69, 164), (37, 34), (16, 1), (8, 2), (2, 9)]
    (codeMat 282) (codeMat 298) (codeMat 270) false
    det282 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2947_lower : 15 ≤ frozenWangTable.L0 (spanCodes [69, 37, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2947_orbit
  simpa only [lower103] using h

theorem space2948_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 133), (48, 3), (8, 2), (5, 32), (2, 40)]
    (codeMat 266) (codeMat 426) (codeMat 335) false
    det266 det426 inv426
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2948_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2948_orbit
  simpa only [lower103] using h

theorem space2949_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [84, 52, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(84, 84), (52, 34), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 417) (codeMat 177) false
    det267 det417 inv417
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2949_lower : 15 ≤ frozenWangTable.L0 (spanCodes [84, 52, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2949_orbit
  simpa only [lower101] using h

theorem space2950_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 96, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 32), (96, 132), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    det273 det273 inv273
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2950_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 96, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2950_orbit
  simpa only [lower103] using h

theorem space2951_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 96, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 32), (96, 164), (17, 11), (9, 9), (3, 3)]
    (codeMat 275) (codeMat 281) (codeMat 281) true
    det275 det281 inv281
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2951_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 96, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2951_orbit
  simpa only [lower103] using h

theorem space2952_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [129, 96, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(129, 35), (96, 175), (17, 11), (9, 9), (3, 3)]
    (codeMat 339) (codeMat 313) (codeMat 313) true
    det339 det313 inv313
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2952_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 96, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2952_orbit
  simpa only [lower103] using h

theorem space2953_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [144, 96, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(144, 32), (96, 134), (8, 2), (2, 8), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) true
    det401 det273 inv273
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2953_lower : 15 ≤ frozenWangTable.L0 (spanCodes [144, 96, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2953_orbit
  simpa only [lower103] using h

theorem space2954_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [129, 96, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(129, 20), (96, 96), (16, 1), (8, 8), (4, 128), (2, 2)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    det266 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2954_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 96, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2954_orbit
  simpa only [lower35] using h

theorem space2955_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [132, 96, 16, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(132, 160), (96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2955_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 96, 16, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 29 space2955_orbit
  simpa only [lower29] using h

theorem space2956_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 65, 33, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 40), (65, 1), (33, 132), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    det85 det273 inv273
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2956_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 65, 33, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2956_orbit
  simpa only [lower103] using h

theorem space2957_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [160, 96, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(160, 164), (96, 132), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) true
    det273 det275 inv275
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2957_lower : 15 ≤ frozenWangTable.L0 (spanCodes [160, 96, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2957_orbit
  simpa only [lower103] using h

theorem space2958_orbit :
    frozenWangTable.OrbitImage 192 (spanCodes [146, 81, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 192 [(146, 511), (81, 383), (49, 33), (10, 42), (7, 1)]
    (codeMat 345) (codeMat 247) (codeMat 379) false
    det345 det247 inv247
    (by rw [basis192]; decide +kernel)
    (by rw [basis192]; decide +kernel)

theorem space2958_lower : 15 ≤ frozenWangTable.L0 (spanCodes [146, 81, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 192 space2958_orbit
  simpa only [lower192] using h

theorem space2959_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [130, 65, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(130, 8), (65, 9), (33, 166), (18, 32), (10, 34)]
    (codeMat 213) (codeMat 313) (codeMat 313) true
    det213 det313 inv313
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2959_lower : 15 ≤ frozenWangTable.L0 (spanCodes [130, 65, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2959_orbit
  simpa only [lower103] using h

theorem space2960_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 67, 35, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 40), (67, 43), (35, 134), (18, 32), (10, 34)]
    (codeMat 215) (codeMat 281) (codeMat 281) true
    det215 det281 inv281
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2960_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 67, 35, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space2960_orbit
  simpa only [lower103] using h

theorem space2961_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [129, 65, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(129, 52), (65, 54), (33, 100), (16, 8), (8, 9), (2, 32)]
    (codeMat 98) (codeMat 281) (codeMat 281) true
    det98 det281 inv281
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2961_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 65, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space2961_orbit
  simpa only [lower31] using h

theorem space2962_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [144, 65, 33, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(144, 40), (65, 3), (33, 132), (8, 2), (2, 32)]
    (codeMat 87) (codeMat 273) (codeMat 273) true
    det87 det273 inv273
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2962_lower : 15 ≤ frozenWangTable.L0 (spanCodes [144, 65, 33, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2962_orbit
  simpa only [lower103] using h

theorem space2963_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [161, 96, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(161, 84), (96, 118), (16, 8), (8, 9), (2, 32)]
    (codeMat 106) (codeMat 281) (codeMat 281) true
    det106 det281 inv281
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2963_lower : 15 ≤ frozenWangTable.L0 (spanCodes [161, 96, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 101 space2963_orbit
  simpa only [lower101] using h

theorem space2964_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [176, 96, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(176, 164), (96, 134), (8, 2), (2, 9), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) true
    det401 det275 inv275
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2964_lower : 15 ≤ frozenWangTable.L0 (spanCodes [176, 96, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2964_orbit
  simpa only [lower103] using h

theorem space2965_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [164, 96, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(164, 252), (96, 104), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    det401 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2965_lower : 15 ≤ frozenWangTable.L0 (spanCodes [164, 96, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2965_orbit
  simpa only [lower35] using h

theorem space2966_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [161, 96, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(161, 244), (96, 224), (17, 11), (9, 8), (4, 128), (3, 2)]
    (codeMat 267) (codeMat 282) (codeMat 267) true
    det267 det282 inv282
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2966_lower : 15 ≤ frozenWangTable.L0 (spanCodes [161, 96, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2966_orbit
  simpa only [lower35] using h

theorem space2967_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [160, 96, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    det273 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2967_lower : 15 ≤ frozenWangTable.L0 (spanCodes [160, 96, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2967_orbit
  simpa only [lower35] using h

theorem space2968_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [259, 67, 35, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(259, 135), (67, 175), (35, 132), (10, 166), (4, 2)]
    (codeMat 207) (codeMat 157) (codeMat 486) true
    det207 det157 inv157
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2968_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 67, 35, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space2968_orbit
  simpa only [lower103] using h

theorem space2969_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 64, 32, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 8), (64, 9), (32, 32), (10, 164), (5, 2)]
    (codeMat 140) (codeMat 169) (codeMat 225) true
    det140 det169 inv169
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2969_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 64, 32, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space2969_orbit
  simpa only [lower103] using h

theorem space2970_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [260, 64, 32, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(260, 8), (64, 3), (32, 32), (10, 132), (1, 2)]
    (codeMat 141) (codeMat 161) (codeMat 161) true
    det141 det161 inv161
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2970_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 64, 32, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2970_orbit
  simpa only [lower103] using h

theorem space2971_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [262, 66, 34, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(262, 173), (66, 135), (34, 164), (10, 132), (1, 2)]
    (codeMat 143) (codeMat 165) (codeMat 163) true
    det143 det165 inv165
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2971_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 66, 34, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space2971_orbit
  simpa only [lower103] using h

theorem space2972_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [288, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(288, 2), (96, 34), (10, 118), (4, 1), (1, 9)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    det305 det141 inv141
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2972_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2972_orbit
  simpa only [lower101] using h

theorem space2973_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [256, 66, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(256, 2), (66, 82), (34, 68), (10, 100), (4, 1), (1, 9)]
    (codeMat 161) (codeMat 141) (codeMat 226) true
    det161 det141 inv141
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2973_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 66, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2973_orbit
  simpa only [lower31] using h

theorem space2974_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 130, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (130, 128), (96, 28), (10, 96), (4, 1), (1, 8)]
    (codeMat 169) (codeMat 140) (codeMat 98) true
    det169 det140 inv140
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2974_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2974_orbit
  simpa only [lower35] using h

theorem space2975_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [291, 160, 96, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(291, 131), (160, 252), (96, 245), (17, 96), (10, 104), (7, 128)]
    (codeMat 95) (codeMat 229) (codeMat 187) false
    det95 det229 inv229
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2975_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 160, 96, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space2975_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
