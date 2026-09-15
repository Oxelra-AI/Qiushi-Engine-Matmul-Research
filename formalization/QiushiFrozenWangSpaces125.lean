import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4000_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [160, 80, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(160, 96), (80, 304), (4, 1), (3, 2)]
    (codeMat 161) (codeMat 204) (codeMat 114) false
    det161 det204 inv204
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4000_lower : 16 ≤ frozenWangTable.L0 (spanCodes [160, 80, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 278 space4000_orbit
  simpa only [lower278] using h

theorem space4001_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [161, 81, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(161, 339), (81, 306), (5, 1), (2, 2)]
    (codeMat 241) (codeMat 380) (codeMat 117) false
    det241 det380 inv380
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4001_lower : 16 ≤ frozenWangTable.L0 (spanCodes [161, 81, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 278 space4001_orbit
  simpa only [lower278] using h

theorem space4002_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [162, 82, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(162, 306), (82, 96), (6, 2), (1, 1)]
    (codeMat 281) (codeMat 417) (codeMat 177) false
    det281 det417 inv417
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4002_lower : 16 ≤ frozenWangTable.L0 (spanCodes [162, 82, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 278 space4002_orbit
  simpa only [lower278] using h

theorem space4003_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [163, 64, 16, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(163, 98), (64, 288), (16, 1), (4, 16)]
    (codeMat 330) (codeMat 98) (codeMat 140) false
    det330 det98 inv98
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4003_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 64, 16, 4]) := by
  have h := frozenWangTable.lower_le_L0 338 space4003_orbit
  simpa only [lower338] using h

theorem space4004_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [163, 64, 18, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(163, 370), (64, 1), (18, 16), (6, 256)]
    (codeMat 92) (codeMat 305) (codeMat 305) false
    det92 det305 inv305
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4004_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 64, 18, 6]) := by
  have h := frozenWangTable.lower_le_L0 336 space4004_orbit
  simpa only [lower336] using h

theorem space4005_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [163, 65, 16, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(163, 98), (65, 1), (16, 16), (5, 288)]
    (codeMat 213) (codeMat 277) (codeMat 277) false
    det213 det277 inv277
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4005_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 65, 16, 5]) := by
  have h := frozenWangTable.lower_le_L0 338 space4005_orbit
  simpa only [lower338] using h

theorem space4006_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [162, 64, 20, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(162, 96), (64, 3), (20, 272), (1, 2)]
    (codeMat 141) (codeMat 161) (codeMat 161) true
    det141 det161 inv161
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4006_lower : 16 ≤ frozenWangTable.L0 (spanCodes [162, 64, 20, 1]) := by
  have h := frozenWangTable.lower_le_L0 276 space4006_orbit
  simpa only [lower276] using h

theorem space4007_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [163, 64, 20, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(163, 337), (64, 1), (20, 306), (8, 2)]
    (codeMat 212) (codeMat 419) (codeMat 183) true
    det212 det419 inv419
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4007_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 64, 20, 8]) := by
  have h := frozenWangTable.lower_le_L0 278 space4007_orbit
  simpa only [lower278] using h

theorem space4008_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [163, 65, 21, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(163, 98), (65, 1), (21, 304), (9, 2)]
    (codeMat 157) (codeMat 165) (codeMat 163) true
    det157 det165 inv165
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4008_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 65, 21, 9]) := by
  have h := frozenWangTable.lower_le_L0 278 space4008_orbit
  simpa only [lower278] using h

theorem space4009_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [163, 73, 24, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(163, 115), (73, 1), (24, 16), (5, 256)]
    (codeMat 87) (codeMat 279) (codeMat 279) false
    det87 det279 inv279
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4009_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 73, 24, 5]) := by
  have h := frozenWangTable.lower_le_L0 336 space4009_orbit
  simpa only [lower336] using h

theorem space4010_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [163, 73, 27, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(163, 355), (73, 1), (27, 16), (6, 256)]
    (codeMat 95) (codeMat 311) (codeMat 307) false
    det95 det311 inv311
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4010_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 73, 27, 6]) := by
  have h := frozenWangTable.lower_le_L0 336 space4010_orbit
  simpa only [lower336] using h

theorem space4011_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [162, 72, 28, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(162, 306), (72, 3), (28, 97), (1, 1)]
    (codeMat 185) (codeMat 279) (codeMat 279) true
    det185 det279 inv279
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4011_lower : 16 ≤ frozenWangTable.L0 (spanCodes [162, 72, 28, 1]) := by
  have h := frozenWangTable.lower_le_L0 278 space4011_orbit
  simpa only [lower278] using h

theorem space4012_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [130, 84, 32, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(130, 16), (84, 354), (32, 1), (1, 256)]
    (codeMat 106) (codeMat 84) (codeMat 84) false
    det106 det84 inv84
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4012_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 84, 32, 1]) := by
  have h := frozenWangTable.lower_le_L0 336 space4012_orbit
  simpa only [lower336] using h

theorem space4013_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [128, 84, 32, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(128, 16), (84, 114), (32, 1), (3, 256)]
    (codeMat 98) (codeMat 92) (codeMat 116) false
    det98 det92 inv92
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4013_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 84, 32, 3]) := by
  have h := frozenWangTable.lower_le_L0 336 space4013_orbit
  simpa only [lower336] using h

theorem space4014_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [131, 80, 32, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(131, 96), (80, 304), (32, 2), (4, 1)]
    (codeMat 273) (codeMat 92) (codeMat 116) true
    det273 det92 inv92
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4014_lower : 16 ≤ frozenWangTable.L0 (spanCodes [131, 80, 32, 4]) := by
  have h := frozenWangTable.lower_le_L0 278 space4014_orbit
  simpa only [lower278] using h

theorem space4015_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [130, 84, 33, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(130, 1), (84, 354), (33, 272), (9, 16)]
    (codeMat 157) (codeMat 298) (codeMat 270) false
    det157 det298 inv298
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4015_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 84, 33, 9]) := by
  have h := frozenWangTable.lower_le_L0 336 space4015_orbit
  simpa only [lower336] using h

theorem space4016_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [139, 80, 40, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(139, 338), (80, 322), (40, 1), (4, 288)]
    (codeMat 442) (codeMat 467) (codeMat 339) false
    det442 det467 inv467
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4016_lower : 16 ≤ frozenWangTable.L0 (spanCodes [139, 80, 40, 4]) := by
  have h := frozenWangTable.lower_le_L0 338 space4016_orbit
  simpa only [lower338] using h

theorem space4017_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [135, 84, 36, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(135, 97), (84, 337), (36, 3), (9, 2)]
    (codeMat 171) (codeMat 172) (codeMat 99) false
    det171 det172 inv172
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4017_lower : 16 ≤ frozenWangTable.L0 (spanCodes [135, 84, 36, 9]) := by
  have h := frozenWangTable.lower_le_L0 278 space4017_orbit
  simpa only [lower278] using h

theorem space4018_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [142, 84, 44, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(142, 115), (84, 98), (44, 304), (1, 16)]
    (codeMat 143) (codeMat 314) (codeMat 271) false
    det143 det314 inv314
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4018_lower : 16 ≤ frozenWangTable.L0 (spanCodes [142, 84, 44, 1]) := by
  have h := frozenWangTable.lower_le_L0 338 space4018_orbit
  simpa only [lower338] using h

theorem space4019_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [140, 84, 45, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(140, 354), (84, 370), (45, 1), (2, 256)]
    (codeMat 115) (codeMat 492) (codeMat 115) false
    det115 det492 inv492
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space4019_lower : 16 ≤ frozenWangTable.L0 (spanCodes [140, 84, 45, 2]) := by
  have h := frozenWangTable.lower_le_L0 336 space4019_orbit
  simpa only [lower336] using h

theorem space4020_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [131, 68, 32, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(131, 96), (68, 336), (32, 2), (16, 1)]
    (codeMat 266) (codeMat 99) (codeMat 172) false
    det266 det99 inv99
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4020_lower : 16 ≤ frozenWangTable.L0 (spanCodes [131, 68, 32, 16]) := by
  have h := frozenWangTable.lower_le_L0 278 space4020_orbit
  simpa only [lower278] using h

theorem space4021_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [130, 68, 33, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(130, 2), (68, 304), (33, 96), (16, 1)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    det106 det266 inv266
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4021_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 68, 33, 16]) := by
  have h := frozenWangTable.lower_le_L0 278 space4021_orbit
  simpa only [lower278] using h

theorem space4022_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [128, 70, 35, 18]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(128, 1), (70, 96), (35, 306), (18, 2)]
    (codeMat 92) (codeMat 102) (codeMat 156) true
    det92 det102 inv102
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4022_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 70, 35, 18]) := by
  have h := frozenWangTable.lower_le_L0 278 space4022_orbit
  simpa only [lower278] using h

theorem space4023_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [143, 73, 44, 29]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(143, 99), (73, 2), (44, 304), (29, 96)]
    (codeMat 143) (codeMat 314) (codeMat 271) false
    det143 det314 inv314
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4023_lower : 16 ≤ frozenWangTable.L0 (spanCodes [143, 73, 44, 29]) := by
  have h := frozenWangTable.lower_le_L0 278 space4023_orbit
  simpa only [lower278] using h

theorem space4024_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [128, 68, 35, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(128, 1), (68, 97), (35, 272), (16, 2)]
    (codeMat 84) (codeMat 99) (codeMat 172) true
    det84 det99 inv99
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space4024_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 68, 35, 16]) := by
  have h := frozenWangTable.lower_le_L0 276 space4024_orbit
  simpa only [lower276] using h

theorem space4025_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [139, 79, 40, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(139, 17), (79, 323), (40, 288), (27, 16)]
    (codeMat 94) (codeMat 303) (codeMat 286) false
    det94 det303 inv303
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4025_lower : 16 ≤ frozenWangTable.L0 (spanCodes [139, 79, 40, 27]) := by
  have h := frozenWangTable.lower_le_L0 338 space4025_orbit
  simpa only [lower338] using h

theorem space4026_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [140, 72, 47, 28]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(140, 337), (72, 3), (47, 96), (28, 336)]
    (codeMat 94) (codeMat 303) (codeMat 286) false
    det94 det303 inv303
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4026_lower : 16 ≤ frozenWangTable.L0 (spanCodes [140, 72, 47, 28]) := by
  have h := frozenWangTable.lower_le_L0 278 space4026_orbit
  simpa only [lower278] using h

theorem space4027_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [144, 84, 49, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(144, 1), (84, 339), (49, 306), (2, 2)]
    (codeMat 206) (codeMat 359) (codeMat 174) true
    det206 det359 inv359
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4027_lower : 16 ≤ frozenWangTable.L0 (spanCodes [144, 84, 49, 2]) := by
  have h := frozenWangTable.lower_le_L0 278 space4027_orbit
  simpa only [lower278] using h

theorem space4028_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [130, 65, 33, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(130, 2), (65, 1), (33, 96), (21, 336)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    det85 det273 inv273
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4028_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 65, 33, 21]) := by
  have h := frozenWangTable.lower_le_L0 278 space4028_orbit
  simpa only [lower278] using h

theorem space4029_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [143, 76, 44, 24]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(143, 99), (76, 96), (44, 304), (24, 2)]
    (codeMat 87) (codeMat 482) (codeMat 143) true
    det87 det482 inv482
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4029_lower : 16 ≤ frozenWangTable.L0 (spanCodes [143, 76, 44, 24]) := by
  have h := frozenWangTable.lower_le_L0 278 space4029_orbit
  simpa only [lower278] using h

theorem space4030_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [140, 79, 47, 27]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(140, 305), (79, 306), (47, 96), (27, 1)]
    (codeMat 115) (codeMat 317) (codeMat 285) true
    det115 det317 inv317
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space4030_lower : 16 ≤ frozenWangTable.L0 (spanCodes [140, 79, 47, 27]) := by
  have h := frozenWangTable.lower_le_L0 278 space4030_orbit
  simpa only [lower278] using h

theorem space4031_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [128, 65, 35, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(128, 16), (65, 288), (35, 323), (21, 322)]
    (codeMat 99) (codeMat 116) (codeMat 92) false
    det99 det116 inv116
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space4031_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 65, 35, 21]) := by
  have h := frozenWangTable.lower_le_L0 338 space4031_orbit
  simpa only [lower338] using h


end QiushiMatmul.FrozenWang
