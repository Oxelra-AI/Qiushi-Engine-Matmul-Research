import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3712_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 100, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 224), (128, 8), (100, 28), (17, 129), (9, 3), (3, 128)]
    (codeMat 99) (codeMat 267) (codeMat 282) false
    det99 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3712_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 100, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3712_orbit
  simpa only [lower35] using h

theorem space3713_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [275, 147, 83, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(275, 443), (147, 440), (83, 441), (55, 411), (10, 118)]
    (codeMat 124) (codeMat 474) (codeMat 395) false
    det124 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3713_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 83, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3713_orbit
  simpa only [lower144] using h

theorem space3714_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 133, 66, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 1), (133, 436), (66, 507), (39, 496), (23, 176), (10, 480)]
    (codeMat 157) (codeMat 141) (codeMat 226) false
    det157 det141 inv141
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3714_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 66, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3714_orbit
  simpa only [lower65] using h

theorem space3715_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 36, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (196, 34), (36, 1), (23, 463), (10, 118)]
    (codeMat 299) (codeMat 214) (codeMat 214) true
    det299 det214 inv214
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3715_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 36, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3715_orbit
  simpa only [lower144] using h

theorem space3716_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 67, 38, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 252), (128, 9), (67, 139), (38, 104), (18, 8), (10, 136)]
    (codeMat 159) (codeMat 267) (codeMat 282) false
    det159 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3716_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 38, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3716_orbit
  simpa only [lower35] using h

theorem space3717_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 64, 38, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (128, 8), (64, 9), (38, 224), (17, 28), (10, 31)]
    (codeMat 124) (codeMat 281) (codeMat 281) true
    det124 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3717_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 38, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3717_orbit
  simpa only [lower35] using h

theorem space3718_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 194, 32, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 252), (194, 224), (32, 9), (18, 128), (10, 136), (7, 3)]
    (codeMat 282) (codeMat 236) (codeMat 123) true
    det282 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3718_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 194, 32, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3718_orbit
  simpa only [lower35] using h

theorem space3719_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 144, 83, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 286), (144, 260), (83, 287), (50, 160), (10, 480), (6, 16)]
    (codeMat 140) (codeMat 489) (codeMat 241) false
    det140 det489 inv489
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3719_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 83, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3719_orbit
  simpa only [lower65] using h

theorem space3720_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 128, 81, 35, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 171), (128, 320), (81, 238), (35, 507), (10, 437), (5, 1)]
    (codeMat 305) (codeMat 494) (codeMat 501) false
    det305 det494 inv494
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3720_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 128, 81, 35, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3720_orbit
  simpa only [lower65] using h

theorem space3721_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 194, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (194, 224), (32, 9), (17, 28), (10, 31), (4, 8)]
    (codeMat 267) (codeMat 205) (codeMat 242) false
    det267 det205 inv205
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3721_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3721_orbit
  simpa only [lower35] using h

theorem space3722_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 145, 64, 37, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 252), (145, 131), (64, 9), (37, 96), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 275) (codeMat 275) false
    det95 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3722_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 145, 64, 37, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3722_orbit
  simpa only [lower35] using h

theorem space3723_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 193, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 252), (193, 96), (49, 131), (9, 128), (4, 9), (3, 8)]
    (codeMat 281) (codeMat 244) (codeMat 95) true
    det281 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3723_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 193, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3723_orbit
  simpa only [lower35] using h

theorem space3724_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 68, 32, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 1), (68, 44), (32, 2), (22, 436), (10, 304), (1, 32)]
    (codeMat 85) (codeMat 156) (codeMat 102) true
    det85 det156 inv156
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3724_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 68, 32, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 55 space3724_orbit
  simpa only [lower55] using h

theorem space3725_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [257, 65, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(257, 368), (65, 432), (33, 53), (18, 63), (10, 62), (7, 32)]
    (codeMat 266) (codeMat 478) (codeMat 445) false
    det266 det478 inv478
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3725_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 65, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 74 space3725_orbit
  simpa only [lower74] using h

theorem space3726_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (66, 139), (34, 134), (19, 404), (10, 166), (4, 2)]
    (codeMat 140) (codeMat 143) (codeMat 482) true
    det140 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3726_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space3726_orbit
  simpa only [lower55] using h

theorem space3727_orbit :
    frozenWangTable.OrbitImage 111 (spanCodes [256, 128, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 111 [(256, 2), (128, 1), (16, 8), (9, 360), (3, 256)]
    (codeMat 84) (codeMat 99) (codeMat 172) false
    det84 det99 inv99
    (by rw [basis111]; decide +kernel)
    (by rw [basis111]; decide +kernel)

theorem space3727_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 111 space3727_orbit
  simpa only [lower111] using h

theorem space3728_orbit :
    frozenWangTable.OrbitImage 143 (spanCodes [272, 149, 48, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 143 [(272, 453), (149, 484), (48, 2), (9, 432), (3, 32)]
    (codeMat 85) (codeMat 460) (codeMat 122) true
    det85 det460 inv460
    (by rw [basis143]; decide +kernel)
    (by rw [basis143]; decide +kernel)

theorem space3728_lower : 14 ≤ frozenWangTable.L0 (spanCodes [272, 149, 48, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 143 space3728_orbit
  simpa only [lower143] using h

theorem space3729_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 131, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (131, 441), (35, 436), (19, 404), (10, 306), (7, 438)]
    (codeMat 156) (codeMat 87) (codeMat 468) true
    det156 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3729_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space3729_orbit
  simpa only [lower55] using h

theorem space3730_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 131, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (131, 139), (35, 134), (19, 166), (10, 306), (4, 2)]
    (codeMat 140) (codeMat 94) (codeMat 500) true
    det140 det94 inv94
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3730_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space3730_orbit
  simpa only [lower55] using h

theorem space3731_orbit :
    frozenWangTable.OrbitImage 111 (spanCodes [257, 128, 65, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 111 [(257, 363), (128, 1), (65, 360), (18, 9), (10, 265)]
    (codeMat 188) (codeMat 355) (codeMat 190) false
    det188 det355 inv355
    (by rw [basis111]; decide +kernel)
    (by rw [basis111]; decide +kernel)

theorem space3731_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 111 space3731_orbit
  simpa only [lower111] using h

theorem space3732_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [257, 160, 97, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(257, 193), (160, 398), (97, 10), (18, 432), (10, 400), (5, 192)]
    (codeMat 85) (codeMat 156) (codeMat 102) false
    det85 det156 inv156
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3732_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 160, 97, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 74 space3732_orbit
  simpa only [lower74] using h

theorem space3733_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 130, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (130, 32), (64, 2), (19, 306), (10, 166), (6, 45)]
    (codeMat 428) (codeMat 140) (codeMat 98) false
    det428 det140 inv140
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3733_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space3733_orbit
  simpa only [lower55] using h

theorem space3734_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [272, 144, 68, 52, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(272, 357), (144, 32), (68, 202), (52, 356), (9, 192), (3, 63)]
    (codeMat 247) (codeMat 141) (codeMat 226) false
    det247 det141 inv141
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3734_lower : 14 ≤ frozenWangTable.L0 (spanCodes [272, 144, 68, 52, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 74 space3734_orbit
  simpa only [lower74] using h

theorem space3735_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [273, 129, 81, 53, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(273, 337), (129, 411), (81, 366), (53, 336), (8, 432), (2, 192)]
    (codeMat 95) (codeMat 94) (codeMat 500) false
    det95 det94 inv94
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3735_lower : 14 ≤ frozenWangTable.L0 (spanCodes [273, 129, 81, 53, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 74 space3735_orbit
  simpa only [lower74] using h

theorem space3736_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [262, 130, 68, 34, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(262, 374), (130, 219), (68, 402), (34, 240), (20, 408), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 314) (codeMat 271) false
    det86 det314 inv314
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3736_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 130, 68, 34, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space3736_orbit
  simpa only [lower17] using h

theorem space3737_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 129, 64, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 135), (129, 132), (64, 2), (33, 170), (18, 438), (10, 406)]
    (codeMat 340) (codeMat 412) (codeMat 111) false
    det340 det412 inv412
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3737_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3737_orbit
  simpa only [lower55] using h

theorem space3738_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 133, 68, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 329), (133, 402), (68, 301), (37, 328), (20, 208), (8, 360), (2, 128)]
    (codeMat 94) (codeMat 85) (codeMat 340) false
    det94 det85 inv85
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3738_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 133, 68, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3738_orbit
  simpa only [lower17] using h

theorem space3739_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [260, 196, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(260, 325), (196, 389), (33, 42), (21, 11), (8, 63), (2, 1)]
    (codeMat 281) (codeMat 335) (codeMat 426) false
    det281 det335 inv335
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3739_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 196, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 74 space3739_orbit
  simpa only [lower74] using h

theorem space3740_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 129, 68, 33, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 329), (129, 191), (68, 301), (33, 328), (21, 312), (9, 360), (3, 128)]
    (codeMat 87) (codeMat 215) (codeMat 342) false
    det87 det215 inv215
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3740_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 68, 33, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3740_orbit
  simpa only [lower17] using h

theorem space3741_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 132, 69, 37, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 323), (132, 263), (69, 197), (37, 408), (21, 440), (9, 360), (3, 128)]
    (codeMat 85) (codeMat 247) (codeMat 379) false
    det85 det247 inv247
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3741_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 132, 69, 37, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3741_orbit
  simpa only [lower17] using h

theorem space3742_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 65, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (128, 2), (65, 438), (33, 441), (19, 306), (10, 166)]
    (codeMat 500) (codeMat 92) (codeMat 116) false
    det500 det92 inv92
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3742_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3742_orbit
  simpa only [lower55] using h

theorem space3743_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 196, 32, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 1), (196, 44), (32, 2), (20, 134), (9, 438), (3, 32)]
    (codeMat 85) (codeMat 207) (codeMat 370) true
    det85 det207 inv207
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3743_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 196, 32, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 55 space3743_orbit
  simpa only [lower55] using h


end QiushiMatmul.FrozenWang
