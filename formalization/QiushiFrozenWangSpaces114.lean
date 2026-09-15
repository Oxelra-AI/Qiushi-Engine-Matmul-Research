import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3648_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 147, 80, 32, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 421), (147, 446), (80, 447), (32, 320), (10, 496), (5, 16)]
    (codeMat 141) (codeMat 477) (codeMat 431) false
    det141 det477 inv477
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3648_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 80, 32, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3648_orbit
  simpa only [lower65] using h

theorem space3649_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 144, 82, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 277), (144, 1), (82, 447), (33, 336), (10, 496), (5, 16)]
    (codeMat 206) (codeMat 335) (codeMat 426) false
    det206 det335 inv335
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3649_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 82, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3649_orbit
  simpa only [lower65] using h

theorem space3650_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [275, 144, 65, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(275, 171), (144, 390), (65, 128), (54, 1), (10, 294)]
    (codeMat 379) (codeMat 444) (codeMat 110) false
    det379 det444 inv444
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3650_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 65, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3650_orbit
  simpa only [lower187] using h

theorem space3651_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 145, 66, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 116), (145, 29), (66, 235), (50, 104), (10, 232), (6, 8)]
    (codeMat 142) (codeMat 395) (codeMat 474) false
    det142 det395 inv395
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3651_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 145, 66, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3651_orbit
  simpa only [lower35] using h

theorem space3652_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 146, 66, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 159), (146, 130), (66, 235), (49, 28), (10, 227), (6, 3)]
    (codeMat 190) (codeMat 394) (codeMat 330) true
    det190 det394 inv394
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3652_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 66, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3652_orbit
  simpa only [lower35] using h

theorem space3653_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 133, 81, 49, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 171), (133, 69), (81, 170), (49, 176), (8, 16), (2, 320)]
    (codeMat 84) (codeMat 174) (codeMat 359) false
    det84 det174 inv174
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3653_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 133, 81, 49, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space3653_orbit
  simpa only [lower65] using h

theorem space3654_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 148, 66, 48, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 150), (148, 20), (66, 105), (48, 128), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 417) (codeMat 177) false
    det143 det417 inv417
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3654_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 148, 66, 48, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3654_orbit
  simpa only [lower35] using h

theorem space3655_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 144, 112, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 245), (144, 130), (112, 20), (10, 97), (6, 9), (1, 8)]
    (codeMat 177) (codeMat 426) (codeMat 335) true
    det177 det426 inv426
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3655_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 144, 112, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3655_orbit
  simpa only [lower35] using h

theorem space3656_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [274, 162, 66, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(274, 252), (162, 255), (66, 186), (10, 184), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 410) (codeMat 331) false
    det142 det410 inv410
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space3656_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 162, 66, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 29 space3656_orbit
  simpa only [lower29] using h

theorem space3657_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 160, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 255), (160, 224), (64, 128), (10, 151), (6, 3), (1, 2)]
    (codeMat 305) (codeMat 410) (codeMat 331) false
    det305 det410 inv410
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3657_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 160, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3657_orbit
  simpa only [lower35] using h

theorem space3658_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 160, 66, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 118), (160, 255), (66, 149), (10, 150), (4, 128), (1, 2)]
    (codeMat 143) (codeMat 403) (codeMat 403) true
    det143 det403 inv403
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3658_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 160, 66, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3658_orbit
  simpa only [lower35] using h

theorem space3659_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 66, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 252), (128, 3), (66, 28), (34, 148), (16, 2), (10, 20)]
    (codeMat 86) (codeMat 298) (codeMat 270) true
    det86 det298 inv298
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3659_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3659_orbit
  simpa only [lower35] using h

theorem space3660_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 129, 70, 37, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 507), (129, 506), (70, 79), (37, 480), (18, 16), (10, 336)]
    (codeMat 156) (codeMat 125) (codeMat 348) false
    det156 det125 inv125
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3660_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 70, 37, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3660_orbit
  simpa only [lower65] using h

theorem space3661_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [261, 133, 70, 37, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(261, 20), (133, 420), (70, 160), (37, 21), (22, 367), (10, 170)]
    (codeMat 334) (codeMat 158) (codeMat 358) true
    det334 det158 inv158
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space3661_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 70, 37, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space3661_orbit
  simpa only [lower80] using h

theorem space3662_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [260, 134, 68, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(260, 432), (134, 462), (68, 180), (37, 420), (23, 475), (10, 191)]
    (codeMat 190) (codeMat 442) (codeMat 334) false
    det190 det442 inv442
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space3662_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 68, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space3662_orbit
  simpa only [lower80] using h

theorem space3663_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [260, 133, 68, 38, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(260, 260), (133, 272), (68, 180), (38, 453), (23, 464), (10, 191)]
    (codeMat 334) (codeMat 397) (codeMat 250) true
    det334 det397 inv397
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space3663_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 38, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space3663_orbit
  simpa only [lower80] using h

theorem space3664_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 64, 33, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (128, 1), (64, 9), (33, 252), (16, 3), (10, 31)]
    (codeMat 116) (codeMat 299) (codeMat 318) true
    det116 det299 inv299
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3664_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 33, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3664_orbit
  simpa only [lower35] using h

theorem space3665_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 70, 37, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 150), (130, 1), (70, 149), (37, 232), (16, 8), (10, 96)]
    (codeMat 213) (codeMat 355) (codeMat 190) false
    det213 det355 inv355
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3665_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 37, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3665_orbit
  simpa only [lower35] using h

theorem space3666_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 130, 66, 35, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 252), (130, 130), (66, 139), (35, 104), (18, 128), (10, 136)]
    (codeMat 214) (codeMat 281) (codeMat 281) false
    det214 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3666_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 35, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3666_orbit
  simpa only [lower35] using h

theorem space3667_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 129, 71, 37, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 497), (129, 490), (71, 287), (37, 496), (18, 16), (10, 336)]
    (codeMat 159) (codeMat 93) (codeMat 372) false
    det159 det93 inv93
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3667_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 71, 37, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3667_orbit
  simpa only [lower65] using h

theorem space3668_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [260, 131, 68, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(260, 432), (131, 378), (68, 180), (33, 420), (23, 356), (10, 191)]
    (codeMat 247) (codeMat 426) (codeMat 335) false
    det247 det426 inv426
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space3668_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 68, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space3668_orbit
  simpa only [lower80] using h

theorem space3669_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 133, 70, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (133, 22), (70, 148), (37, 224), (23, 31), (10, 252)]
    (codeMat 111) (codeMat 346) (codeMat 459) true
    det111 det346 inv346
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3669_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 70, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3669_orbit
  simpa only [lower35] using h

theorem space3670_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [275, 147, 83, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(275, 117), (147, 118), (83, 119), (50, 408), (10, 440)]
    (codeMat 84) (codeMat 477) (codeMat 431) false
    det84 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3670_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 83, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3670_orbit
  simpa only [lower144] using h

theorem space3671_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 135, 70, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 497), (135, 245), (70, 287), (33, 496), (18, 320), (10, 336)]
    (codeMat 214) (codeMat 207) (codeMat 370) false
    det214 det207 inv207
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3671_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 70, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3671_orbit
  simpa only [lower65] using h

theorem space3672_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 134, 71, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 507), (134, 437), (71, 79), (33, 480), (18, 320), (10, 336)]
    (codeMat 212) (codeMat 239) (codeMat 351) false
    det212 det239 inv239
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3672_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 71, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3672_orbit
  simpa only [lower65] using h

theorem space3673_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 64, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (128, 1), (64, 9), (34, 148), (16, 2), (10, 22)]
    (codeMat 84) (codeMat 299) (codeMat 318) true
    det84 det299 inv299
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3673_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3673_orbit
  simpa only [lower35] using h

theorem space3674_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 66, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 224), (128, 3), (66, 31), (32, 128), (16, 2), (10, 22)]
    (codeMat 86) (codeMat 267) (codeMat 282) true
    det86 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3674_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3674_orbit
  simpa only [lower35] using h

theorem space3675_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 128, 65, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 480), (128, 320), (65, 16), (39, 507), (20, 437), (10, 506)]
    (codeMat 299) (codeMat 174) (codeMat 359) false
    det299 det174 inv174
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3675_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 128, 65, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3675_orbit
  simpa only [lower65] using h

theorem space3676_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 132, 97, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 1), (132, 26), (97, 69), (21, 160), (8, 320), (2, 16)]
    (codeMat 141) (codeMat 85) (codeMat 340) false
    det141 det85 inv85
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3676_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 97, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space3676_orbit
  simpa only [lower65] using h

theorem space3677_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [272, 149, 80, 52, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(272, 507), (149, 447), (80, 506), (52, 480), (9, 16), (3, 320)]
    (codeMat 92) (codeMat 190) (codeMat 355) false
    det92 det190 inv190
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3677_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 149, 80, 52, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space3677_orbit
  simpa only [lower65] using h

theorem space3678_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [275, 144, 65, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(275, 171), (144, 32), (65, 390), (34, 295), (10, 294)]
    (codeMat 498) (codeMat 492) (codeMat 115) false
    det498 det492 inv492
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3678_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 65, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3678_orbit
  simpa only [lower187] using h

theorem space3679_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 71, 33, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 150), (132, 148), (71, 149), (33, 232), (17, 104), (10, 96)]
    (codeMat 157) (codeMat 481) (codeMat 185) false
    det157 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3679_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 33, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3679_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
