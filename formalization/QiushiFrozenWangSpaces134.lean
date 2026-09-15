import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4288_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 129, 64, 34, 20, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (129, 149), (64, 2), (34, 104), (20, 96), (8, 128)]
    (codeMat 156) (codeMat 394) (codeMat 330) false
    det156 det394 inv394
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4288_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 20, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4288_orbit
  simpa only [lower35] using h

theorem space4289_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 75, 32, 24, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (131, 224), (75, 255), (32, 1), (24, 3), (7, 128)]
    (codeMat 98) (codeMat 205) (codeMat 242) false
    det98 det205 inv205
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4289_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 75, 32, 24, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space4289_orbit
  simpa only [lower35] using h

theorem space4290_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [266, 137, 75, 42, 25, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(266, 99), (137, 126), (75, 139), (42, 227), (25, 252), (6, 3)]
    (codeMat 183) (codeMat 458) (codeMat 458) true
    det183 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4290_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 137, 75, 42, 25, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space4290_orbit
  simpa only [lower35] using h

theorem space4291_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [267, 137, 74, 42, 24, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(267, 244), (137, 149), (74, 23), (42, 232), (24, 128), (6, 8)]
    (codeMat 143) (codeMat 459) (codeMat 346) false
    det143 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4291_lower : 15 ≤ frozenWangTable.L0 (spanCodes [267, 137, 74, 42, 24, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space4291_orbit
  simpa only [lower35] using h

theorem space4292_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 138, 64, 41, 17, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 446), (138, 255), (64, 260), (41, 160), (17, 480), (5, 16)]
    (codeMat 142) (codeMat 498) (codeMat 206) false
    det142 det498 inv498
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4292_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 138, 64, 41, 17, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space4292_orbit
  simpa only [lower65] using h

theorem space4293_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 138, 65, 41, 16, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 446), (138, 69), (65, 260), (41, 160), (16, 320), (5, 16)]
    (codeMat 143) (codeMat 482) (codeMat 143) false
    det143 det482 inv482
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4293_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 138, 65, 41, 16, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space4293_orbit
  simpa only [lower65] using h

theorem space4294_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [269, 140, 73, 44, 29, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(269, 119), (140, 156), (73, 130), (44, 252), (29, 31), (3, 3)]
    (codeMat 190) (codeMat 481) (codeMat 185) true
    det190 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4294_lower : 15 ≤ frozenWangTable.L0 (spanCodes [269, 140, 73, 44, 29, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4294_orbit
  simpa only [lower35] using h

theorem space4295_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [265, 140, 77, 44, 25, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(265, 246), (140, 124), (77, 29), (44, 232), (25, 96), (3, 8)]
    (codeMat 206) (codeMat 481) (codeMat 185) false
    det206 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4295_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 140, 77, 44, 25, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4295_orbit
  simpa only [lower35] using h

theorem space4296_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [272, 137, 81, 41, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(272, 68), (137, 245), (81, 246), (41, 176), (5, 16), (3, 24)]
    (codeMat 142) (codeMat 458) (codeMat 458) false
    det142 det458 inv458
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4296_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 137, 81, 41, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 29 space4296_orbit
  simpa only [lower29] using h

theorem space4297_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [269, 133, 64, 36, 20, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(269, 245), (133, 176), (64, 320), (36, 27), (20, 26), (2, 16)]
    (codeMat 266) (codeMat 117) (codeMat 380) false
    det266 det117 inv117
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4297_lower : 15 ≤ frozenWangTable.L0 (spanCodes [269, 133, 64, 36, 20, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space4297_orbit
  simpa only [lower65] using h

theorem space4298_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [264, 133, 69, 36, 17, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(264, 362), (133, 452), (69, 453), (36, 16), (17, 96), (2, 256)]
    (codeMat 92) (codeMat 225) (codeMat 169) false
    det92 det225 inv225
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4298_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 133, 69, 36, 17, 2]) := by
  have h := frozenWangTable.lower_le_L0 69 space4298_orbit
  simpa only [lower69] using h

theorem space4299_orbit :
    frozenWangTable.OrbitImage 113 (spanCodes [144, 84, 48, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 113 [(144, 2), (84, 99), (48, 384), (2, 1), (1, 9)]
    (codeMat 305) (codeMat 271) (codeMat 314) true
    det305 det271 inv271
    (by rw [basis113]; decide +kernel)
    (by rw [basis113]; decide +kernel)

theorem space4299_lower : 14 ≤ frozenWangTable.L0 (spanCodes [144, 84, 48, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 113 space4299_orbit
  simpa only [lower113] using h

theorem space4300_orbit :
    frozenWangTable.OrbitImage 113 (spanCodes [146, 84, 48, 8, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 113 [(146, 384), (84, 106), (48, 2), (8, 1), (1, 9)]
    (codeMat 474) (codeMat 401) (codeMat 401) false
    det474 det401 inv401
    (by rw [basis113]; decide +kernel)
    (by rw [basis113]; decide +kernel)

theorem space4300_lower : 14 ≤ frozenWangTable.L0 (spanCodes [146, 84, 48, 8, 1]) := by
  have h := frozenWangTable.lower_le_L0 113 space4300_orbit
  simpa only [lower113] using h

theorem space4301_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [132, 69, 36, 17, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(132, 136), (69, 440), (36, 1), (17, 34), (13, 14), (3, 32)]
    (codeMat 267) (codeMat 92) (codeMat 116) false
    det267 det92 inv92
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space4301_lower : 14 ≤ frozenWangTable.L0 (spanCodes [132, 69, 36, 17, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 55 space4301_orbit
  simpa only [lower55] using h

theorem space4302_orbit :
    frozenWangTable.OrbitImage 114 (spanCodes [130, 65, 33, 21, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 114 [(130, 2), (65, 1), (33, 264), (21, 416), (9, 8)]
    (codeMat 157) (codeMat 277) (codeMat 277) false
    det157 det277 inv277
    (by rw [basis114]; decide +kernel)
    (by rw [basis114]; decide +kernel)

theorem space4302_lower : 14 ≤ frozenWangTable.L0 (spanCodes [130, 65, 33, 21, 9]) := by
  have h := frozenWangTable.lower_le_L0 114 space4302_orbit
  simpa only [lower114] using h

theorem space4303_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [131, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(131, 389), (64, 192), (32, 32), (19, 53), (10, 30), (7, 1)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    det273 det409 inv409
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space4303_lower : 14 ≤ frozenWangTable.L0 (spanCodes [131, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 74 space4303_orbit
  simpa only [lower74] using h

theorem space4304_orbit :
    frozenWangTable.OrbitImage 114 (spanCodes [272, 144, 84, 48, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 114 [(272, 11), (144, 3), (84, 163), (48, 9), (3, 256)]
    (codeMat 102) (codeMat 123) (codeMat 236) false
    det102 det123 inv123
    (by rw [basis114]; decide +kernel)
    (by rw [basis114]; decide +kernel)

theorem space4304_lower : 14 ≤ frozenWangTable.L0 (spanCodes [272, 144, 84, 48, 3]) := by
  have h := frozenWangTable.lower_le_L0 114 space4304_orbit
  simpa only [lower114] using h

theorem space4305_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [272, 146, 80, 49, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(272, 223), (146, 63), (80, 367), (49, 324), (9, 325), (4, 192)]
    (codeMat 106) (codeMat 247) (codeMat 379) false
    det106 det247 inv247
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space4305_lower : 14 ≤ frozenWangTable.L0 (spanCodes [272, 146, 80, 49, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 74 space4305_orbit
  simpa only [lower74] using h

theorem space4306_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [258, 134, 66, 36, 22, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(258, 53), (134, 30), (66, 21), (36, 192), (22, 347), (1, 63)]
    (codeMat 229) (codeMat 239) (codeMat 351) false
    det229 det239 inv239
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space4306_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 134, 66, 36, 22, 1]) := by
  have h := frozenWangTable.lower_le_L0 74 space4306_orbit
  simpa only [lower74] using h

theorem space4307_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 134, 69, 37, 17, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 14), (134, 441), (69, 15), (37, 35), (17, 316), (8, 32)]
    (codeMat 188) (codeMat 174) (codeMat 359) true
    det188 det174 inv174
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space4307_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 134, 69, 37, 17, 8]) := by
  have h := frozenWangTable.lower_le_L0 55 space4307_orbit
  simpa only [lower55] using h

theorem space4308_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 133, 65, 38, 21, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 439), (133, 15), (65, 438), (38, 168), (21, 47), (11, 170)]
    (codeMat 412) (codeMat 377) (codeMat 369) true
    det412 det377 inv377
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space4308_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 38, 21, 11]) := by
  have h := frozenWangTable.lower_le_L0 55 space4308_orbit
  simpa only [lower55] using h

theorem space4309_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 134, 68, 36, 16, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 100), (134, 301), (68, 402), (36, 32), (16, 360), (14, 208), (1, 128)]
    (codeMat 94) (codeMat 394) (codeMat 330) false
    det94 det394 inv394
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4309_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 134, 68, 36, 16, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space4309_orbit
  simpa only [lower17] using h

theorem space4310_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [268, 137, 72, 40, 28, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(268, 224), (137, 398), (72, 63), (40, 192), (28, 388), (2, 1)]
    (codeMat 185) (codeMat 331) (codeMat 410) false
    det185 det331 inv331
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space4310_lower : 14 ≤ frozenWangTable.L0 (spanCodes [268, 137, 72, 40, 28, 2]) := by
  have h := frozenWangTable.lower_le_L0 74 space4310_orbit
  simpa only [lower74] using h

theorem space4311_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 132, 69, 37, 17, 13, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 263), (132, 322), (69, 451), (37, 312), (17, 208), (13, 280), (2, 128)]
    (codeMat 85) (codeMat 317) (codeMat 285) false
    det85 det317 inv317
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4311_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 132, 69, 37, 17, 13, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space4311_orbit
  simpa only [lower17] using h

theorem space4312_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 132, 64, 36, 20, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 228), (132, 329), (64, 219), (36, 32), (20, 328), (13, 280), (3, 128)]
    (codeMat 94) (codeMat 267) (codeMat 282) false
    det94 det267 inv267
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4312_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 132, 64, 36, 20, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space4312_orbit
  simpa only [lower17] using h

theorem space4313_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 132, 65, 36, 21, 12, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 68), (132, 451), (65, 1), (36, 32), (21, 408), (12, 328), (3, 128)]
    (codeMat 93) (codeMat 275) (codeMat 275) false
    det93 det275 inv275
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4313_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 132, 65, 36, 21, 12, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space4313_orbit
  simpa only [lower17] using h

theorem space4314_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 133, 69, 36, 17, 13, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 196), (133, 450), (69, 451), (36, 32), (17, 80), (13, 280), (2, 128)]
    (codeMat 92) (codeMat 281) (codeMat 281) false
    det92 det281 inv281
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4314_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 133, 69, 36, 17, 13, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space4314_orbit
  simpa only [lower17] using h

theorem space4315_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 35, 19, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 274), (128, 63), (67, 228), (35, 80), (19, 312), (9, 32), (4, 128)]
    (codeMat 95) (codeMat 242) (codeMat 205) false
    det95 det242 inv242
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4315_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 19, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space4315_orbit
  simpa only [lower17] using h

theorem space4316_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 35, 17, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 100), (128, 219), (66, 429), (35, 160), (17, 408), (8, 360), (7, 128)]
    (codeMat 94) (codeMat 339) (codeMat 467) false
    det94 det339 inv339
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4316_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 35, 17, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4316_orbit
  simpa only [lower17] using h

theorem space4317_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 33, 17, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 196), (130, 1), (64, 390), (33, 160), (17, 456), (11, 112), (5, 128)]
    (codeMat 93) (codeMat 330) (codeMat 394) false
    det93 det330 inv330
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4317_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 33, 17, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space4317_orbit
  simpa only [lower17] using h

theorem space4318_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 66, 34, 17, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 329), (129, 374), (66, 429), (34, 456), (17, 240), (8, 360), (7, 128)]
    (codeMat 95) (codeMat 213) (codeMat 470) false
    det95 det213 inv213
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4318_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 17, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4318_orbit
  simpa only [lower17] using h

theorem space4319_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 66, 33, 17, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 451), (130, 390), (66, 391), (33, 280), (17, 112), (11, 440), (7, 128)]
    (codeMat 92) (codeMat 253) (codeMat 415) false
    det92 det253 inv253
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4319_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 33, 17, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4319_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
