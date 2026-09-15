import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3520_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [273, 64, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(273, 84), (64, 1), (8, 2), (2, 32)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    det84 det273 inv273
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3520_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 64, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space3520_orbit
  simpa only [lower267] using h

theorem space3521_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [272, 64, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(272, 118), (64, 1), (9, 2), (3, 32)]
    (codeMat 92) (codeMat 275) (codeMat 275) true
    det92 det275 inv275
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3521_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 64, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space3521_orbit
  simpa only [lower267] using h

theorem space3522_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 65, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 3), (65, 1), (23, 304), (10, 96)]
    (codeMat 141) (codeMat 165) (codeMat 163) false
    det141 det165 inv165
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3522_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 65, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3522_orbit
  simpa only [lower278] using h

theorem space3523_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 83, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (83, 336), (10, 96), (5, 1)]
    (codeMat 169) (codeMat 172) (codeMat 99) true
    det169 det172 inv172
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3523_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 83, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 278 space3523_orbit
  simpa only [lower278] using h

theorem space3524_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 66, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (66, 338), (51, 96), (10, 336)]
    (codeMat 94) (codeMat 190) (codeMat 355) false
    det94 det190 inv190
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3524_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 66, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3524_orbit
  simpa only [lower278] using h

theorem space3525_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 67, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 115), (67, 338), (50, 323), (10, 322)]
    (codeMat 122) (codeMat 426) (codeMat 335) false
    det122 det426 inv426
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3525_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 67, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space3525_orbit
  simpa only [lower338] using h

theorem space3526_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 83, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (83, 96), (34, 306), (10, 304)]
    (codeMat 214) (codeMat 468) (codeMat 87) true
    det214 det468 inv468
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3526_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 83, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3526_orbit
  simpa only [lower278] using h

theorem space3527_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [263, 65, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(263, 280), (65, 16), (39, 259), (20, 326), (10, 258)]
    (codeMat 107) (codeMat 188) (codeMat 103) false
    det107 det188 inv188
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3527_lower : 16 ≤ frozenWangTable.L0 (spanCodes [263, 65, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3527_orbit
  simpa only [lower150] using h

theorem space3528_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 66, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 305), (66, 338), (54, 1), (10, 322)]
    (codeMat 115) (codeMat 442) (codeMat 334) false
    det115 det442 inv442
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3528_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 66, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space3528_orbit
  simpa only [lower338] using h

theorem space3529_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 67, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 307), (67, 338), (55, 304), (10, 336)]
    (codeMat 87) (codeMat 174) (codeMat 359) false
    det87 det174 inv174
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3529_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 67, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3529_orbit
  simpa only [lower278] using h

theorem space3530_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 83, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (83, 336), (39, 306), (10, 304)]
    (codeMat 159) (codeMat 340) (codeMat 85) true
    det159 det340 inv340
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3530_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 83, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3530_orbit
  simpa only [lower278] using h

theorem space3531_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 113, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 369), (113, 96), (10, 274), (5, 2)]
    (codeMat 143) (codeMat 342) (codeMat 215) true
    det143 det342 inv342
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3531_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 113, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 276 space3531_orbit
  simpa only [lower276] using h

theorem space3532_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [273, 128, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(273, 84), (128, 1), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    det140 det266 inv266
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3532_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 128, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space3532_orbit
  simpa only [lower267] using h

theorem space3533_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [257, 128, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(257, 118), (128, 1), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    det156 det267 inv267
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3533_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 128, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space3533_orbit
  simpa only [lower267] using h

theorem space3534_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 130, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 3), (130, 2), (23, 336), (10, 304)]
    (codeMat 93) (codeMat 124) (codeMat 124) false
    det93 det124 inv124
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3534_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 130, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3534_orbit
  simpa only [lower278] using h

theorem space3535_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 146, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 305), (146, 16), (10, 322), (7, 1)]
    (codeMat 185) (codeMat 369) (codeMat 377) false
    det185 det369 inv369
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3535_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 146, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 338 space3535_orbit
  simpa only [lower338] using h

theorem space3536_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 147, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (147, 336), (10, 304), (6, 2)]
    (codeMat 205) (codeMat 460) (codeMat 122) true
    det205 det460 inv460
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3536_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 278 space3536_orbit
  simpa only [lower278] using h

theorem space3537_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 144, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (144, 1), (51, 336), (10, 96)]
    (codeMat 86) (codeMat 102) (codeMat 156) false
    det86 det102 inv102
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3537_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3537_orbit
  simpa only [lower278] using h

theorem space3538_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 147, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 307), (147, 304), (48, 1), (10, 96)]
    (codeMat 114) (codeMat 116) (codeMat 92) true
    det114 det116 inv116
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3538_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3538_orbit
  simpa only [lower278] using h

theorem space3539_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 130, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 115), (130, 16), (39, 323), (10, 322)]
    (codeMat 171) (codeMat 377) (codeMat 369) false
    det171 det377 inv377
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3539_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 130, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space3539_orbit
  simpa only [lower338] using h

theorem space3540_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 146, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (146, 2), (55, 96), (10, 336)]
    (codeMat 143) (codeMat 117) (codeMat 380) false
    det143 det117 inv117
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3540_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 146, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3540_orbit
  simpa only [lower278] using h

theorem space3541_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 147, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (147, 96), (54, 2), (10, 304)]
    (codeMat 95) (codeMat 396) (codeMat 106) true
    det95 det396 inv396
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3541_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3541_orbit
  simpa only [lower278] using h

theorem space3542_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 149, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 99), (149, 96), (48, 2), (10, 274)]
    (codeMat 87) (codeMat 397) (codeMat 250) true
    det87 det397 inv397
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3542_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 149, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3542_orbit
  simpa only [lower276] using h

theorem space3543_orbit :
    frozenWangTable.OrbitImage 275 (spanCodes [275, 163, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 275 [(275, 86), (163, 85), (10, 162), (6, 2)]
    (codeMat 143) (codeMat 394) (codeMat 330) true
    det143 det394 inv394
    (by rw [basis275]; decide +kernel)
    (by rw [basis275]; decide +kernel)

theorem space3543_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 163, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 275 space3543_orbit
  simpa only [lower275] using h

theorem space3544_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 144, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 94), (144, 16), (49, 68), (10, 258), (6, 1)]
    (codeMat 177) (codeMat 116) (codeMat 92) false
    det177 det116 inv116
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3544_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 150 space3544_orbit
  simpa only [lower150] using h

theorem space3545_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [260, 135, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(260, 16), (135, 280), (33, 258), (23, 259), (10, 326)]
    (codeMat 107) (codeMat 122) (codeMat 460) false
    det107 det122 inv122
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3545_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 135, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3545_orbit
  simpa only [lower150] using h

theorem space3546_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 144, 83, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 417), (144, 32), (83, 33), (10, 42)]
    (codeMat 405) (codeMat 317) (codeMat 285) true
    det405 det317 inv317
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3546_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 83, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3546_orbit
  simpa only [lower298] using h

theorem space3547_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [272, 192, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(272, 118), (192, 1), (9, 32), (3, 2)]
    (codeMat 204) (codeMat 282) (codeMat 267) true
    det204 det282 inv282
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3547_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 192, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space3547_orbit
  simpa only [lower267] using h

theorem space3548_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 147, 80, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 342), (147, 333), (80, 332), (10, 264), (5, 16)]
    (codeMat 205) (codeMat 482) (codeMat 143) false
    det205 det482 inv482
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3548_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 80, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 150 space3548_orbit
  simpa only [lower150] using h

theorem space3549_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 130, 83, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 395), (130, 1), (83, 11), (10, 42)]
    (codeMat 477) (codeMat 303) (codeMat 286) true
    det477 det303 inv303
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3549_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 130, 83, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3549_orbit
  simpa only [lower298] using h

theorem space3550_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 147, 66, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 417), (147, 33), (66, 43), (10, 42)]
    (codeMat 478) (codeMat 311) (codeMat 307) true
    det478 det311 inv311
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3550_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 66, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3550_orbit
  simpa only [lower298] using h

theorem space3551_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 165, 116, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 369), (165, 370), (116, 98), (10, 274)]
    (codeMat 239) (codeMat 492) (codeMat 115) false
    det239 det492 inv492
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3551_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 165, 116, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3551_orbit
  simpa only [lower276] using h


end QiushiMatmul.FrozenWang
