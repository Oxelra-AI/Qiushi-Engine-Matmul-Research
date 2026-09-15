import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4224_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 133, 66, 38, 22, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 436), (133, 78), (66, 437), (38, 176), (22, 160), (9, 320)]
    (codeMat 212) (codeMat 465) (codeMat 465) false
    det212 det465 inv465
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4224_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 66, 38, 22, 9]) := by
  have h := frozenWangTable.lower_le_L0 65 space4224_orbit
  simpa only [lower65] using h

theorem space4225_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 67, 32, 23, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 22), (131, 148), (67, 150), (32, 9), (23, 104), (15, 105)]
    (codeMat 98) (codeMat 253) (codeMat 415) true
    det98 det253 inv253
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4225_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 23, 15]) := by
  have h := frozenWangTable.lower_le_L0 35 space4225_orbit
  simpa only [lower35] using h

theorem space4226_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 135, 68, 36, 16, 13]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 506), (135, 437), (68, 436), (36, 16), (16, 320), (13, 176)]
    (codeMat 157) (codeMat 226) (codeMat 141) false
    det157 det226 inv226
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4226_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 68, 36, 16, 13]) := by
  have h := frozenWangTable.lower_le_L0 65 space4226_orbit
  simpa only [lower65] using h

theorem space4227_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [263, 134, 64, 37, 20, 13]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(263, 170), (134, 463), (64, 260), (37, 283), (20, 127), (13, 475)]
    (codeMat 174) (codeMat 500) (codeMat 94) false
    det174 det500 inv500
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4227_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 64, 37, 20, 13]) := by
  have h := frozenWangTable.lower_le_L0 80 space4227_orbit
  simpa only [lower80] using h

theorem space4228_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 67, 32, 23, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (131, 150), (67, 148), (32, 8), (23, 232), (12, 104)]
    (codeMat 212) (codeMat 212) (codeMat 86) false
    det212 det212 inv212
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4228_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 23, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4228_orbit
  simpa only [lower35] using h

theorem space4229_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 148, 84, 52, 12, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (148, 246), (84, 244), (52, 232), (12, 224), (3, 128)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    det84 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4229_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 148, 84, 52, 12, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4229_orbit
  simpa only [lower35] using h

theorem space4230_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [264, 134, 66, 36, 22, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(264, 430), (134, 420), (66, 475), (36, 432), (22, 160), (1, 192)]
    (codeMat 87) (codeMat 425) (codeMat 249) false
    det87 det425 inv425
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4230_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 134, 66, 36, 22, 1]) := by
  have h := frozenWangTable.lower_le_L0 80 space4230_orbit
  simpa only [lower80] using h

theorem space4231_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [288, 162, 68, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(288, 260), (162, 228), (68, 176), (16, 27), (10, 10), (1, 16)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    det331 det282 inv282
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4231_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 162, 68, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4231_orbit
  simpa only [lower65] using h

theorem space4232_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [264, 131, 64, 32, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(264, 68), (131, 272), (64, 256), (32, 1), (20, 78)]
    (codeMat 298) (codeMat 212) (codeMat 86) false
    det298 det212 inv212
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4232_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 131, 64, 32, 20]) := by
  have h := frozenWangTable.lower_le_L0 149 space4232_orbit
  simpa only [lower149] using h

theorem space4233_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 133, 65, 38, 21, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 148), (133, 22), (65, 128), (38, 252), (21, 31), (12, 224)]
    (codeMat 110) (codeMat 370) (codeMat 207) true
    det110 det370 inv370
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4233_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 65, 38, 21, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4233_orbit
  simpa only [lower35] using h

theorem space4234_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 67, 33, 23, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (130, 8), (67, 105), (33, 148), (23, 20), (12, 150)]
    (codeMat 93) (codeMat 377) (codeMat 369) true
    det93 det377 inv377
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4234_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 67, 33, 23, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4234_orbit
  simpa only [lower35] using h

theorem space4235_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [259, 130, 70, 33, 18, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(259, 68), (130, 3), (70, 70), (33, 160), (18, 24), (12, 176)]
    (codeMat 93) (codeMat 346) (codeMat 459) false
    det93 det346 inv346
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4235_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 33, 18, 12]) := by
  have h := frozenWangTable.lower_le_L0 29 space4235_orbit
  simpa only [lower29] using h

theorem space4236_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 68, 35, 16, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 126), (128, 130), (68, 119), (35, 232), (16, 128), (14, 224)]
    (codeMat 158) (codeMat 377) (codeMat 369) false
    det158 det377 inv377
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4236_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 68, 35, 16, 14]) := by
  have h := frozenWangTable.lower_le_L0 35 space4236_orbit
  simpa only [lower35] using h

theorem space4237_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 131, 65, 32, 21, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 136), (131, 104), (65, 8), (32, 3), (21, 148), (8, 1)]
    (codeMat 298) (codeMat 165) (codeMat 163) false
    det298 det165 inv165
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4237_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 21, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4237_orbit
  simpa only [lower35] using h

theorem space4238_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 135, 67, 36, 23, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 224), (135, 28), (67, 227), (36, 128), (23, 20), (9, 130)]
    (codeMat 94) (codeMat 337) (codeMat 337) true
    det94 det337 inv337
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4238_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 67, 36, 23, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4238_orbit
  simpa only [lower35] using h

theorem space4239_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 67, 32, 23, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (131, 104), (67, 96), (32, 3), (23, 252), (11, 224)]
    (codeMat 116) (codeMat 212) (codeMat 86) true
    det116 det212 inv212
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4239_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 23, 11]) := by
  have h := frozenWangTable.lower_le_L0 35 space4239_orbit
  simpa only [lower35] using h

theorem space4240_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 128, 73, 35, 25, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 10), (128, 16), (73, 260), (35, 78), (25, 436), (4, 1)]
    (codeMat 417) (codeMat 84) (codeMat 84) false
    det417 det84 inv84
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4240_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 73, 35, 25, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space4240_orbit
  simpa only [lower65] using h

theorem space4241_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [265, 137, 75, 42, 26, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(265, 126), (137, 252), (75, 31), (42, 96), (26, 224), (5, 8)]
    (codeMat 142) (codeMat 489) (codeMat 241) false
    det142 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4241_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 137, 75, 42, 26, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space4241_orbit
  simpa only [lower35] using h

theorem space4242_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [267, 138, 74, 41, 27, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(267, 124), (138, 151), (74, 21), (41, 96), (27, 128), (5, 8)]
    (codeMat 207) (codeMat 467) (codeMat 339) false
    det207 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4242_lower : 15 ≤ frozenWangTable.L0 (spanCodes [267, 138, 74, 41, 27, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space4242_orbit
  simpa only [lower35] using h

theorem space4243_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 146, 83, 49, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 507), (146, 27), (83, 430), (49, 261), (8, 320), (7, 1)]
    (codeMat 177) (codeMat 375) (codeMat 491) false
    det177 det375 inv375
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4243_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 83, 49, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4243_orbit
  simpa only [lower65] using h

theorem space4244_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 146, 83, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 260), (146, 1), (83, 447), (49, 336), (10, 496), (7, 16)]
    (codeMat 207) (codeMat 331) (codeMat 410) false
    det207 det331 inv331
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4244_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 146, 83, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4244_orbit
  simpa only [lower65] using h

theorem space4245_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 130, 83, 33, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 156), (130, 3), (83, 29), (33, 96), (11, 232), (7, 128)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    det93 det339 inv339
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4245_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 130, 83, 33, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space4245_orbit
  simpa only [lower35] using h

theorem space4246_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [268, 138, 76, 41, 24]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(268, 53), (138, 52), (76, 245), (41, 414), (24, 16)]
    (codeMat 277) (codeMat 460) (codeMat 122) false
    det277 det460 inv460
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4246_lower : 15 ≤ frozenWangTable.L0 (spanCodes [268, 138, 76, 41, 24]) := by
  have h := frozenWangTable.lower_le_L0 220 space4246_orbit
  simpa only [lower220] using h

theorem space4247_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 131, 65, 32, 21, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 1), (131, 104), (65, 8), (32, 3), (21, 252), (12, 28)]
    (codeMat 125) (codeMat 156) (codeMat 102) true
    det125 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4247_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 65, 32, 21, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4247_orbit
  simpa only [lower35] using h

theorem space4248_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [263, 132, 71, 39, 19, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(263, 272), (132, 420), (71, 20), (39, 464), (19, 367), (14, 21)]
    (codeMat 271) (codeMat 403) (codeMat 403) true
    det271 det403 inv403
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4248_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 132, 71, 39, 19, 14]) := by
  have h := frozenWangTable.lower_le_L0 80 space4248_orbit
  simpa only [lower80] using h

theorem space4249_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 133, 70, 38, 18, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 78), (133, 506), (70, 507), (38, 160), (18, 16), (14, 480)]
    (codeMat 157) (codeMat 313) (codeMat 313) false
    det157 det313 inv313
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4249_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 70, 38, 18, 14]) := by
  have h := frozenWangTable.lower_le_L0 65 space4249_orbit
  simpa only [lower65] using h

theorem space4250_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 131, 69, 32, 17, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 3), (131, 224), (69, 28), (32, 1), (17, 96), (8, 8)]
    (codeMat 122) (codeMat 140) (codeMat 98) true
    det122 det140 inv140
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4250_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 69, 32, 17, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4250_orbit
  simpa only [lower35] using h

theorem space4251_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [289, 163, 72, 24, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(289, 68), (163, 351), (72, 325), (24, 16), (4, 256)]
    (codeMat 87) (codeMat 467) (codeMat 339) false
    det87 det467 inv467
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4251_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 163, 72, 24, 4]) := by
  have h := frozenWangTable.lower_le_L0 149 space4251_orbit
  simpa only [lower149] using h

theorem space4252_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [265, 129, 66, 34, 18, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(265, 238), (129, 160), (66, 176), (34, 261), (18, 260), (4, 320)]
    (codeMat 106) (codeMat 460) (codeMat 122) false
    det106 det460 inv460
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4252_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 129, 66, 34, 18, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space4252_orbit
  simpa only [lower65] using h

theorem space4253_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [288, 163, 65, 17, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(288, 130), (163, 116), (65, 9), (17, 96), (8, 8), (4, 128)]
    (codeMat 87) (codeMat 161) (codeMat 161) false
    det87 det161 inv161
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4253_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 163, 65, 17, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space4253_orbit
  simpa only [lower35] using h

theorem space4254_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 147, 83, 48, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 261), (147, 437), (83, 245), (48, 16), (9, 27), (7, 1)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    det273 det409 inv409
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4254_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 147, 83, 48, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4254_orbit
  simpa only [lower65] using h

theorem space4255_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 163, 64, 19, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 430), (163, 421), (64, 1), (19, 352), (11, 96), (7, 16)]
    (codeMat 140) (codeMat 419) (codeMat 183) false
    det140 det419 inv419
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4255_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 163, 64, 19, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space4255_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
