import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4032_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [135, 70, 36, 18]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(135, 336), (70, 96), (36, 3), (18, 2)]
    (codeMat 99) (codeMat 116) (codeMat 92) false
    det99 det116 inv116
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4032_lower : 16 ≤ frozenWangTable.L0 (spanCodes [135, 70, 36, 18]) := by
  have h := frozenWangTable.lower_le_L0 278 space4032_orbit
  simpa only [lower278] using h

theorem space4033_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [142, 79, 45, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(142, 98), (79, 368), (45, 1), (27, 2)]
    (codeMat 115) (codeMat 492) (codeMat 115) false
    det115 det492 inv492
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4033_lower : 16 ≤ frozenWangTable.L0 (spanCodes [142, 79, 45, 27]) := by
  have h := frozenWangTable.lower_le_L0 276 space4033_orbit
  simpa only [lower276] using h

theorem space4034_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [147, 82, 48, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(147, 336), (82, 96), (48, 3), (6, 2)]
    (codeMat 267) (codeMat 396) (codeMat 106) true
    det267 det396 inv396
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4034_lower : 16 ≤ frozenWangTable.L0 (spanCodes [147, 82, 48, 6]) := by
  have h := frozenWangTable.lower_le_L0 278 space4034_orbit
  simpa only [lower278] using h

theorem space4035_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [144, 81, 51, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(144, 16), (81, 338), (51, 289), (5, 1)]
    (codeMat 369) (codeMat 377) (codeMat 369) false
    det369 det377 inv377
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4035_lower : 16 ≤ frozenWangTable.L0 (spanCodes [144, 81, 51, 5]) := by
  have h := frozenWangTable.lower_le_L0 338 space4035_orbit
  simpa only [lower338] using h

theorem space4036_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [128, 64, 35, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(128, 2), (64, 3), (35, 96), (20, 272)]
    (codeMat 84) (codeMat 281) (codeMat 281) false
    det84 det281 inv281
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4036_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 64, 35, 20]) := by
  have h := frozenWangTable.lower_le_L0 276 space4036_orbit
  simpa only [lower276] using h

theorem space4037_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [143, 79, 44, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(143, 99), (79, 96), (44, 274), (27, 2)]
    (codeMat 95) (codeMat 486) (codeMat 157) true
    det95 det486 inv486
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4037_lower : 16 ≤ frozenWangTable.L0 (spanCodes [143, 79, 44, 27]) := by
  have h := frozenWangTable.lower_le_L0 276 space4037_orbit
  simpa only [lower276] using h

theorem space4038_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [144, 80, 51, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(144, 288), (80, 304), (51, 322), (4, 1)]
    (codeMat 161) (codeMat 204) (codeMat 114) false
    det161 det204 inv204
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4038_lower : 16 ≤ frozenWangTable.L0 (spanCodes [144, 80, 51, 4]) := by
  have h := frozenWangTable.lower_le_L0 338 space4038_orbit
  simpa only [lower338] using h

theorem space4039_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [148, 84, 52, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(148, 336), (84, 337), (52, 304), (3, 2)]
    (codeMat 140) (codeMat 225) (codeMat 169) true
    det140 det225 inv225
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4039_lower : 16 ≤ frozenWangTable.L0 (spanCodes [148, 84, 52, 3]) := by
  have h := frozenWangTable.lower_le_L0 278 space4039_orbit
  simpa only [lower278] using h

theorem space4040_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [148, 84, 54, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(148, 322), (84, 98), (54, 16), (1, 1)]
    (codeMat 473) (codeMat 423) (codeMat 181) false
    det473 det423 inv423
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4040_lower : 16 ≤ frozenWangTable.L0 (spanCodes [148, 84, 54, 1]) := by
  have h := frozenWangTable.lower_le_L0 338 space4040_orbit
  simpa only [lower338] using h

theorem space4041_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [128, 79, 35, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(128, 288), (79, 338), (35, 17), (27, 1)]
    (codeMat 403) (codeMat 229) (codeMat 187) false
    det403 det229 inv229
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4041_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 79, 35, 27]) := by
  have h := frozenWangTable.lower_le_L0 338 space4041_orbit
  simpa only [lower338] using h

theorem space4042_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [139, 68, 40, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(139, 272), (68, 97), (40, 1), (16, 2)]
    (codeMat 234) (codeMat 340) (codeMat 85) false
    det234 det340 inv340
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4042_lower : 16 ≤ frozenWangTable.L0 (spanCodes [139, 68, 40, 16]) := by
  have h := frozenWangTable.lower_le_L0 276 space4042_orbit
  simpa only [lower276] using h

theorem space4043_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [143, 64, 44, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(143, 115), (64, 16), (44, 322), (20, 323)]
    (codeMat 226) (codeMat 412) (codeMat 111) false
    det226 det412 inv412
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4043_lower : 16 ≤ frozenWangTable.L0 (spanCodes [143, 64, 44, 20]) := by
  have h := frozenWangTable.lower_le_L0 338 space4043_orbit
  simpa only [lower338] using h

theorem space4044_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [142, 65, 45, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(142, 99), (65, 16), (45, 1), (21, 289)]
    (codeMat 491) (codeMat 174) (codeMat 359) false
    det491 det174 inv174
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4044_lower : 16 ≤ frozenWangTable.L0 (spanCodes [142, 65, 45, 21]) := by
  have h := frozenWangTable.lower_le_L0 338 space4044_orbit
  simpa only [lower338] using h

theorem space4045_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [147, 84, 48, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(147, 306), (84, 339), (48, 3), (8, 2)]
    (codeMat 226) (codeMat 412) (codeMat 111) false
    det226 det412 inv412
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4045_lower : 16 ≤ frozenWangTable.L0 (spanCodes [147, 84, 48, 8]) := by
  have h := frozenWangTable.lower_le_L0 278 space4045_orbit
  simpa only [lower278] using h

theorem space4046_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [135, 79, 36, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(135, 338), (79, 306), (36, 3), (27, 1)]
    (codeMat 275) (codeMat 230) (codeMat 159) false
    det275 det230 inv230
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4046_lower : 16 ≤ frozenWangTable.L0 (spanCodes [135, 79, 36, 27]) := by
  have h := frozenWangTable.lower_le_L0 278 space4046_orbit
  simpa only [lower278] using h

theorem space4047_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [140, 68, 47, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(140, 99), (68, 371), (47, 257), (16, 256)]
    (codeMat 179) (codeMat 236) (codeMat 123) false
    det179 det236 inv236
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4047_lower : 16 ≤ frozenWangTable.L0 (spanCodes [140, 68, 47, 16]) := by
  have h := frozenWangTable.lower_le_L0 336 space4047_orbit
  simpa only [lower336] using h

theorem space4048_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [148, 84, 55, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(148, 371), (84, 355), (55, 257), (8, 256)]
    (codeMat 163) (codeMat 244) (codeMat 95) false
    det163 det244 inv244
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4048_lower : 16 ≤ frozenWangTable.L0 (spanCodes [148, 84, 55, 8]) := by
  have h := frozenWangTable.lower_le_L0 336 space4048_orbit
  simpa only [lower336] using h

theorem space4049_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [155, 83, 56, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(155, 304), (83, 336), (56, 1), (7, 3)]
    (codeMat 282) (codeMat 244) (codeMat 95) true
    det282 det244 inv244
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4049_lower : 16 ≤ frozenWangTable.L0 (spanCodes [155, 83, 56, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space4049_orbit
  simpa only [lower278] using h

theorem space4050_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [256, 163, 84, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(256, 16), (163, 99), (84, 370), (8, 256)]
    (codeMat 167) (codeMat 242) (codeMat 205) false
    det167 det242 inv242
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4050_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 163, 84, 8]) := by
  have h := frozenWangTable.lower_le_L0 336 space4050_orbit
  simpa only [lower336] using h

theorem space4051_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [264, 163, 83, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(264, 338), (163, 98), (83, 306), (7, 3)]
    (codeMat 247) (codeMat 431) (codeMat 477) true
    det247 det431 inv431
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4051_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 163, 83, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space4051_orbit
  simpa only [lower278] using h

theorem space4052_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [264, 163, 79, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(264, 323), (163, 98), (79, 17), (27, 288)]
    (codeMat 318) (codeMat 443) (codeMat 254) false
    det318 det443 inv443
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4052_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 163, 79, 27]) := by
  have h := frozenWangTable.lower_le_L0 338 space4052_orbit
  simpa only [lower338] using h

theorem space4053_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [271, 163, 72, 28]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(271, 305), (163, 98), (72, 3), (28, 338)]
    (codeMat 254) (codeMat 445) (codeMat 478) false
    det254 det445 inv445
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4053_lower : 16 ≤ frozenWangTable.L0 (spanCodes [271, 163, 72, 28]) := by
  have h := frozenWangTable.lower_le_L0 278 space4053_orbit
  simpa only [lower278] using h

theorem space4054_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [273, 161, 84, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(273, 354), (161, 370), (84, 355), (2, 256)]
    (codeMat 117) (codeMat 489) (codeMat 241) false
    det117 det489 inv489
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4054_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 161, 84, 2]) := by
  have h := frozenWangTable.lower_le_L0 336 space4054_orbit
  simpa only [lower336] using h

theorem space4055_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [256, 163, 64, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(256, 2), (163, 305), (64, 1), (20, 338)]
    (codeMat 188) (codeMat 179) (codeMat 421) false
    det188 det179 inv179
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4055_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 163, 64, 20]) := by
  have h := frozenWangTable.lower_le_L0 278 space4055_orbit
  simpa only [lower278] using h

theorem space4056_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [273, 163, 81, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(273, 337), (163, 305), (81, 338), (5, 1)]
    (codeMat 425) (codeMat 489) (codeMat 241) true
    det425 det489 inv489
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4056_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 163, 81, 5]) := by
  have h := frozenWangTable.lower_le_L0 278 space4056_orbit
  simpa only [lower278] using h

theorem space4057_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [256, 163, 65, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(256, 256), (163, 99), (65, 1), (21, 371)]
    (codeMat 317) (codeMat 401) (codeMat 401) false
    det317 det401 inv401
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4057_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 163, 65, 21]) := by
  have h := frozenWangTable.lower_le_L0 336 space4057_orbit
  simpa only [lower336] using h

theorem space4058_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [264, 139, 84, 40]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(264, 17), (139, 323), (84, 98), (40, 16)]
    (codeMat 342) (codeMat 157) (codeMat 486) false
    det342 det157 inv157
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4058_lower : 16 ≤ frozenWangTable.L0 (spanCodes [264, 139, 84, 40]) := by
  have h := frozenWangTable.lower_le_L0 338 space4058_orbit
  simpa only [lower338] using h

theorem space4059_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 144, 84, 51]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 275), (144, 3), (84, 99), (51, 274)]
    (codeMat 102) (codeMat 95) (codeMat 244) false
    det102 det95 inv95
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4059_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 84, 51]) := by
  have h := frozenWangTable.lower_le_L0 276 space4059_orbit
  simpa only [lower276] using h

theorem space4060_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [271, 143, 84, 44]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(271, 354), (143, 98), (84, 99), (44, 371)]
    (codeMat 311) (codeMat 254) (codeMat 443) false
    det311 det254 inv254
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4060_lower : 16 ≤ frozenWangTable.L0 (spanCodes [271, 143, 84, 44]) := by
  have h := frozenWangTable.lower_le_L0 336 space4060_orbit
  simpa only [lower336] using h

theorem space4061_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 147, 84, 48]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (147, 97), (84, 337), (48, 3)]
    (codeMat 102) (codeMat 459) (codeMat 346) true
    det102 det459 inv459
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4061_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 84, 48]) := by
  have h := frozenWangTable.lower_le_L0 278 space4061_orbit
  simpa only [lower278] using h

theorem space4062_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 148, 84, 55]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 306), (148, 304), (84, 305), (55, 338)]
    (codeMat 116) (codeMat 473) (codeMat 409) false
    det116 det473 inv473
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4062_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 148, 84, 55]) := by
  have h := frozenWangTable.lower_le_L0 278 space4062_orbit
  simpa only [lower278] using h

theorem space4063_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [288, 160, 84, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(288, 1), (160, 17), (84, 99), (3, 256)]
    (codeMat 102) (codeMat 95) (codeMat 244) false
    det102 det95 inv95
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4063_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 160, 84, 3]) := by
  have h := frozenWangTable.lower_le_L0 336 space4063_orbit
  simpa only [lower336] using h


end QiushiMatmul.FrozenWang
