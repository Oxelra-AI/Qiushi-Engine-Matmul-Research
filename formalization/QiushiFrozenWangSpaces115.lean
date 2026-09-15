import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3680_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 64, 35, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 96), (128, 1), (64, 9), (35, 224), (16, 3), (10, 31)]
    (codeMat 116) (codeMat 267) (codeMat 282) true
    det116 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3680_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 35, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3680_orbit
  simpa only [lower35] using h

theorem space3681_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 135, 70, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 252), (135, 28), (70, 255), (34, 104), (16, 8), (10, 105)]
    (codeMat 122) (codeMat 377) (codeMat 369) true
    det122 det377 inv377
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3681_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 70, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3681_orbit
  simpa only [lower35] using h

theorem space3682_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 71, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (130, 130), (71, 148), (33, 224), (23, 227), (10, 252)]
    (codeMat 110) (codeMat 458) (codeMat 458) true
    det110 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3682_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 71, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3682_orbit
  simpa only [lower35] using h

theorem space3683_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 135, 70, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 252), (135, 139), (70, 126), (39, 104), (21, 136), (10, 232)]
    (codeMat 215) (codeMat 346) (codeMat 459) false
    det215 det346 inv346
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3683_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 70, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3683_orbit
  simpa only [lower35] using h

theorem space3684_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 144, 64, 33, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 116), (144, 2), (64, 9), (33, 96), (8, 8), (2, 128)]
    (codeMat 86) (codeMat 273) (codeMat 273) false
    det86 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3684_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 144, 64, 33, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space3684_orbit
  simpa only [lower35] using h

theorem space3685_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 132, 66, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 320), (132, 336), (66, 480), (37, 437), (23, 79), (10, 507)]
    (codeMat 354) (codeMat 415) (codeMat 253) false
    det354 det415 inv415
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3685_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 66, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3685_orbit
  simpa only [lower65] using h

theorem space3686_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 134, 66, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (134, 238), (66, 497), (39, 480), (23, 160), (10, 496)]
    (codeMat 158) (codeMat 181) (codeMat 423) false
    det158 det181 inv181
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3686_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 66, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3686_orbit
  simpa only [lower65] using h

theorem space3687_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 70, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 96), (130, 1), (70, 105), (32, 128), (16, 2), (10, 150)]
    (codeMat 85) (codeMat 331) (codeMat 410) true
    det85 det331 inv331
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3687_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3687_orbit
  simpa only [lower35] using h

theorem space3688_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 70, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 232), (128, 128), (70, 224), (34, 150), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 377) (codeMat 369) false
    det298 det377 inv377
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3688_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 70, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3688_orbit
  simpa only [lower35] using h

theorem space3689_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 64, 37, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (128, 8), (64, 9), (37, 252), (17, 28), (10, 31)]
    (codeMat 124) (codeMat 313) (codeMat 313) true
    det124 det313 inv313
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3689_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 37, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3689_orbit
  simpa only [lower35] using h

theorem space3690_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 146, 83, 49, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 421), (146, 1), (83, 446), (49, 160), (10, 496), (4, 320)]
    (codeMat 95) (codeMat 334) (codeMat 442) false
    det95 det334 inv334
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3690_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 83, 49, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space3690_orbit
  simpa only [lower65] using h

theorem space3691_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 193, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (193, 224), (32, 9), (17, 28), (10, 31), (4, 8)]
    (codeMat 331) (codeMat 205) (codeMat 242) false
    det331 det205 inv205
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3691_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 193, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3691_orbit
  simpa only [lower35] using h

theorem space3692_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 147, 80, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 187), (147, 447), (80, 446), (50, 480), (10, 496), (5, 320)]
    (codeMat 85) (codeMat 254) (codeMat 443) false
    det85 det254 inv254
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3692_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 80, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3692_orbit
  simpa only [lower65] using h

theorem space3693_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 129, 66, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 177), (129, 255), (66, 228), (50, 496), (10, 480), (5, 320)]
    (codeMat 87) (codeMat 214) (codeMat 214) false
    det87 det214 inv214
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3693_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 129, 66, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3693_orbit
  simpa only [lower65] using h

theorem space3694_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 144, 83, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 331), (144, 320), (83, 347), (49, 78), (10, 437), (6, 1)]
    (codeMat 417) (codeMat 458) (codeMat 458) false
    det417 det458 inv458
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3694_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 83, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3694_orbit
  simpa only [lower65] using h

theorem space3695_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 146, 83, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 187), (146, 1), (83, 447), (51, 160), (10, 496), (6, 16)]
    (codeMat 207) (codeMat 111) (codeMat 412) false
    det207 det111 inv111
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3695_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 83, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3695_orbit
  simpa only [lower65] using h

theorem space3696_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 146, 65, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 286), (146, 27), (65, 260), (33, 176), (10, 480), (6, 320)]
    (codeMat 92) (codeMat 370) (codeMat 207) false
    det92 det370 inv370
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3696_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 65, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3696_orbit
  simpa only [lower65] using h

theorem space3697_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 64, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (128, 8), (64, 9), (36, 128), (17, 20), (10, 22)]
    (codeMat 92) (codeMat 281) (codeMat 281) true
    det92 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3697_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3697_orbit
  simpa only [lower35] using h

theorem space3698_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 192, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (192, 128), (32, 9), (17, 20), (10, 22), (4, 8)]
    (codeMat 267) (codeMat 204) (codeMat 114) false
    det267 det204 inv204
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3698_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 192, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3698_orbit
  simpa only [lower35] using h

theorem space3699_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [275, 144, 65, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(275, 397), (144, 128), (65, 390), (39, 295), (10, 294)]
    (codeMat 443) (codeMat 380) (codeMat 117) false
    det443 det380 inv380
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3699_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 65, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3699_orbit
  simpa only [lower187] using h

theorem space3700_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 134, 66, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 78), (134, 79), (66, 507), (39, 160), (21, 336), (10, 480)]
    (codeMat 212) (codeMat 443) (codeMat 254) false
    det212 det443 inv443
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3700_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 66, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3700_orbit
  simpa only [lower65] using h

theorem space3701_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 67, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 96), (130, 8), (67, 97), (34, 224), (21, 28), (10, 227)]
    (codeMat 125) (codeMat 337) (codeMat 337) true
    det125 det337 inv337
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3701_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 67, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3701_orbit
  simpa only [lower35] using h

theorem space3702_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [259, 130, 70, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(259, 68), (130, 2), (70, 71), (34, 160), (16, 16), (10, 184)]
    (codeMat 85) (codeMat 345) (codeMat 345) false
    det85 det345 inv345
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space3702_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space3702_orbit
  simpa only [lower29] using h

theorem space3703_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 133, 65, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 148), (133, 20), (65, 130), (34, 104), (16, 8), (10, 97)]
    (codeMat 106) (codeMat 369) (codeMat 377) true
    det106 det369 inv369
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3703_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 65, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3703_orbit
  simpa only [lower35] using h

theorem space3704_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 64, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (128, 8), (64, 9), (39, 148), (17, 20), (10, 22)]
    (codeMat 92) (codeMat 313) (codeMat 313) true
    det92 det313 inv313
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3704_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3704_orbit
  simpa only [lower35] using h

theorem space3705_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 71, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (132, 104), (71, 105), (36, 128), (17, 148), (10, 150)]
    (codeMat 93) (codeMat 473) (codeMat 409) true
    det93 det473 inv473
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3705_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3705_orbit
  simpa only [lower35] using h

theorem space3706_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 146, 81, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 177), (146, 27), (81, 287), (51, 176), (10, 480), (6, 16)]
    (codeMat 206) (codeMat 95) (codeMat 244) false
    det206 det95 inv95
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3706_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 81, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3706_orbit
  simpa only [lower65] using h

theorem space3707_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 130, 81, 34, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 156), (130, 3), (81, 29), (34, 224), (10, 232), (7, 128)]
    (codeMat 85) (codeMat 339) (codeMat 467) false
    det85 det339 inv339
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3707_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 81, 34, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3707_orbit
  simpa only [lower35] using h

theorem space3708_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 195, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (195, 128), (32, 9), (17, 20), (10, 22), (4, 8)]
    (codeMat 331) (codeMat 204) (codeMat 114) false
    det331 det204 inv204
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3708_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 195, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3708_orbit
  simpa only [lower35] using h

theorem space3709_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 97, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 246), (130, 9), (97, 20), (16, 8), (10, 96), (5, 128)]
    (codeMat 87) (codeMat 354) (codeMat 142) false
    det87 det354 inv354
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3709_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 97, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space3709_orbit
  simpa only [lower35] using h

theorem space3710_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 148, 81, 49, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 161), (148, 69), (81, 186), (49, 160), (8, 16), (2, 320)]
    (codeMat 86) (codeMat 142) (codeMat 354) false
    det86 det142 inv142
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3710_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 148, 81, 49, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space3710_orbit
  simpa only [lower65] using h

theorem space3711_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 132, 101, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (132, 26), (101, 245), (21, 176), (8, 320), (2, 16)]
    (codeMat 140) (codeMat 117) (codeMat 380) false
    det140 det117 inv117
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3711_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 101, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space3711_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
