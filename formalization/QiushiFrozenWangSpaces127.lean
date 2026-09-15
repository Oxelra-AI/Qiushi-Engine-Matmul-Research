import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4064_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [256, 135, 84, 36]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(256, 2), (135, 338), (84, 307), (36, 3)]
    (codeMat 167) (codeMat 158) (codeMat 358) true
    det167 det158 inv158
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4064_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 135, 84, 36]) := by
  have h := frozenWangTable.lower_le_L0 278 space4064_orbit
  simpa only [lower278] using h

theorem space4065_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [264, 143, 84, 44]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(264, 272), (143, 369), (84, 370), (44, 274)]
    (codeMat 167) (codeMat 242) (codeMat 205) false
    det167 det242 inv242
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4065_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 143, 84, 44]) := by
  have h := frozenWangTable.lower_le_L0 276 space4065_orbit
  simpa only [lower276] using h

theorem space4066_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 148, 84, 55]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 114), (148, 304), (84, 305), (55, 338)]
    (codeMat 116) (codeMat 473) (codeMat 409) false
    det116 det473 inv473
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4066_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 148, 84, 55]) := by
  have h := frozenWangTable.lower_le_L0 338 space4066_orbit
  simpa only [lower338] using h

theorem space4067_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [277, 146, 84, 49]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(277, 339), (146, 3), (84, 307), (49, 338)]
    (codeMat 111) (codeMat 87) (codeMat 468) false
    det111 det87 inv87
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4067_lower : 16 ≤ frozenWangTable.L0 (spanCodes [277, 146, 84, 49]) := by
  have h := frozenWangTable.lower_le_L0 278 space4067_orbit
  simpa only [lower278] using h

theorem space4068_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [288, 163, 80, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(288, 2), (163, 370), (80, 274), (4, 3)]
    (codeMat 183) (codeMat 159) (codeMat 230) true
    det183 det159 inv159
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4068_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 163, 80, 4]) := by
  have h := frozenWangTable.lower_le_L0 276 space4068_orbit
  simpa only [lower276] using h

theorem space4069_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [264, 142, 84, 45]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(264, 338), (142, 114), (84, 305), (45, 16)]
    (codeMat 415) (codeMat 375) (codeMat 491) false
    det415 det375 inv375
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4069_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 142, 84, 45]) := by
  have h := frozenWangTable.lower_le_L0 338 space4069_orbit
  simpa only [lower338] using h

theorem space4070_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [273, 151, 84, 52]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(273, 305), (151, 304), (84, 307), (52, 97)]
    (codeMat 397) (codeMat 461) (codeMat 234) false
    det397 det461 inv461
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4070_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 151, 84, 52]) := by
  have h := frozenWangTable.lower_le_L0 278 space4070_orbit
  simpa only [lower278] using h

theorem space4071_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 149, 84, 54]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 98), (149, 96), (84, 370), (54, 3)]
    (codeMat 110) (codeMat 461) (codeMat 234) true
    det110 det461 inv461
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4071_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 149, 84, 54]) := by
  have h := frozenWangTable.lower_le_L0 276 space4071_orbit
  simpa only [lower276] using h

theorem space4072_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [277, 147, 84, 48]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(277, 307), (147, 306), (84, 339), (48, 3)]
    (codeMat 125) (codeMat 122) (codeMat 460) true
    det125 det122 inv122
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4072_lower : 16 ≤ frozenWangTable.L0 (spanCodes [277, 147, 84, 48]) := by
  have h := frozenWangTable.lower_le_L0 278 space4072_orbit
  simpa only [lower278] using h

theorem space4073_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [288, 163, 81, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(288, 288), (163, 305), (81, 323), (5, 16)]
    (codeMat 461) (codeMat 458) (codeMat 458) false
    det461 det458 inv458
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4073_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 163, 81, 5]) := by
  have h := frozenWangTable.lower_le_L0 338 space4073_orbit
  simpa only [lower338] using h

theorem space4074_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [292, 162, 84, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(292, 1), (162, 17), (84, 339), (1, 288)]
    (codeMat 303) (codeMat 86) (codeMat 212) false
    det303 det86 inv86
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4074_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 162, 84, 1]) := by
  have h := frozenWangTable.lower_le_L0 338 space4074_orbit
  simpa only [lower338] using h

theorem space4075_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [264, 155, 84, 56]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(264, 368), (155, 97), (84, 275), (56, 3)]
    (codeMat 239) (codeMat 426) (codeMat 335) true
    det239 det426 inv426
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4075_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 155, 84, 56]) := by
  have h := frozenWangTable.lower_le_L0 276 space4075_orbit
  simpa only [lower276] using h

theorem space4076_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 128, 84, 35]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 115), (128, 1), (84, 98), (35, 338)]
    (codeMat 236) (codeMat 334) (codeMat 442) false
    det236 det334 inv334
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4076_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 128, 84, 35]) := by
  have h := frozenWangTable.lower_le_L0 338 space4076_orbit
  simpa only [lower338] using h

theorem space4077_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [288, 163, 68, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(288, 16), (163, 339), (68, 322), (16, 288)]
    (codeMat 309) (codeMat 233) (codeMat 233) false
    det309 det233 inv233
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4077_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 163, 68, 16]) := by
  have h := frozenWangTable.lower_le_L0 338 space4077_orbit
  simpa only [lower338] using h

theorem space4078_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [292, 163, 64, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(292, 16), (163, 305), (64, 1), (20, 338)]
    (codeMat 188) (codeMat 179) (codeMat 421) false
    det188 det179 inv179
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4078_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 163, 64, 20]) := by
  have h := frozenWangTable.lower_le_L0 338 space4078_orbit
  simpa only [lower338] using h

theorem space4079_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [293, 163, 65, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(293, 371), (163, 370), (65, 3), (21, 274)]
    (codeMat 229) (codeMat 397) (codeMat 250) false
    det229 det397 inv397
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4079_lower : 16 ≤ frozenWangTable.L0 (spanCodes [293, 163, 65, 21]) := by
  have h := frozenWangTable.lower_le_L0 276 space4079_orbit
  simpa only [lower276] using h

theorem space4080_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [260, 144, 84, 51]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(260, 16), (144, 1), (84, 273), (51, 371)]
    (codeMat 302) (codeMat 107) (codeMat 428) false
    det302 det107 inv107
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4080_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 144, 84, 51]) := by
  have h := frozenWangTable.lower_le_L0 336 space4080_orbit
  simpa only [lower336] using h

theorem space4081_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 128, 84, 35]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 97), (128, 1), (84, 98), (35, 338)]
    (codeMat 236) (codeMat 334) (codeMat 442) false
    det236 det334 inv334
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4081_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 128, 84, 35]) := by
  have h := frozenWangTable.lower_le_L0 278 space4081_orbit
  simpa only [lower278] using h

theorem space4082_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [293, 163, 70, 18]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(293, 371), (163, 370), (70, 17), (18, 256)]
    (codeMat 229) (codeMat 397) (codeMat 250) false
    det229 det397 inv397
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4082_lower : 16 ≤ frozenWangTable.L0 (spanCodes [293, 163, 70, 18]) := by
  have h := frozenWangTable.lower_le_L0 336 space4082_orbit
  simpa only [lower336] using h

theorem space4083_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [304, 163, 83, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(304, 336), (163, 307), (83, 97), (7, 3)]
    (codeMat 229) (codeMat 369) (codeMat 377) true
    det229 det369 inv369
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4083_lower : 16 ≤ frozenWangTable.L0 (spanCodes [304, 163, 83, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space4083_orbit
  simpa only [lower278] using h

theorem space4084_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [264, 146, 84, 49]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(264, 306), (146, 3), (84, 337), (49, 97)]
    (codeMat 351) (codeMat 370) (codeMat 207) false
    det351 det370 inv370
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4084_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 146, 84, 49]) := by
  have h := frozenWangTable.lower_le_L0 278 space4084_orbit
  simpa only [lower278] using h

theorem space4085_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [271, 149, 84, 54]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(271, 99), (149, 17), (84, 354), (54, 256)]
    (codeMat 247) (codeMat 382) (codeMat 499) false
    det247 det382 inv382
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4085_lower : 16 ≤ frozenWangTable.L0 (spanCodes [271, 149, 84, 54]) := by
  have h := frozenWangTable.lower_le_L0 336 space4085_orbit
  simpa only [lower336] using h

theorem space4086_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 142, 84, 45]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 306), (142, 99), (84, 305), (45, 1)]
    (codeMat 379) (codeMat 342) (codeMat 215) true
    det379 det342 inv342
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4086_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 142, 84, 45]) := by
  have h := frozenWangTable.lower_le_L0 278 space4086_orbit
  simpa only [lower278] using h

theorem space4087_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [304, 163, 84, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(304, 371), (163, 273), (84, 114), (9, 256)]
    (codeMat 239) (codeMat 342) (codeMat 215) false
    det239 det342 inv342
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4087_lower : 16 ≤ frozenWangTable.L0 (spanCodes [304, 163, 84, 9]) := by
  have h := frozenWangTable.lower_le_L0 336 space4087_orbit
  simpa only [lower336] using h

theorem space4088_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [260, 155, 84, 56]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(260, 16), (155, 371), (84, 273), (56, 256)]
    (codeMat 174) (codeMat 171) (codeMat 485) false
    det174 det171 inv171
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4088_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 155, 84, 56]) := by
  have h := frozenWangTable.lower_le_L0 336 space4088_orbit
  simpa only [lower336] using h

theorem space4089_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 139, 84, 40]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 97), (139, 306), (84, 98), (40, 1)]
    (codeMat 370) (codeMat 171) (codeMat 485) true
    det370 det171 inv171
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4089_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 139, 84, 40]) := by
  have h := frozenWangTable.lower_le_L0 278 space4089_orbit
  simpa only [lower278] using h

theorem space4090_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [288, 163, 72, 28]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(288, 1), (163, 339), (72, 3), (28, 97)]
    (codeMat 342) (codeMat 157) (codeMat 486) false
    det342 det157 inv157
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4090_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 163, 72, 28]) := by
  have h := frozenWangTable.lower_le_L0 278 space4090_orbit
  simpa only [lower278] using h

theorem space4091_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [292, 163, 76, 24]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(292, 16), (163, 355), (76, 17), (24, 256)]
    (codeMat 190) (codeMat 187) (codeMat 229) false
    det190 det187 inv187
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4091_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 163, 76, 24]) := by
  have h := frozenWangTable.lower_le_L0 336 space4091_orbit
  simpa only [lower336] using h

theorem space4092_orbit :
    frozenWangTable.OrbitImage 147 (spanCodes [275, 138, 81, 41, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 147 [(275, 94), (138, 255), (81, 228), (41, 160), (5, 16)]
    (codeMat 142) (codeMat 498) (codeMat 206) false
    det142 det498 inv498
    (by rw [basis147]; decide +kernel)
    (by rw [basis147]; decide +kernel)

theorem space4092_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 138, 81, 41, 5]) := by
  have h := frozenWangTable.lower_le_L0 147 space4092_orbit
  simpa only [lower147] using h

theorem space4093_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [160, 64, 20, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(160, 224), (64, 128), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    det273 det282 inv282
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4093_lower : 15 ≤ frozenWangTable.L0 (spanCodes [160, 64, 20, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4093_orbit
  simpa only [lower35] using h

theorem space4094_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [162, 66, 16, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(162, 126), (66, 22), (16, 9), (8, 1), (6, 130), (1, 2)]
    (codeMat 266) (codeMat 307) (codeMat 311) true
    det266 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4094_lower : 15 ≤ frozenWangTable.L0 (spanCodes [162, 66, 16, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4094_orbit
  simpa only [lower35] using h

theorem space4095_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [162, 66, 18, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(162, 246), (66, 22), (18, 9), (8, 3), (4, 128), (1, 2)]
    (codeMat 267) (codeMat 275) (codeMat 275) true
    det267 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4095_lower : 15 ≤ frozenWangTable.L0 (spanCodes [162, 66, 18, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4095_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
