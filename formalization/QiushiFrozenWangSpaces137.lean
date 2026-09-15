import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4384_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 140, 72, 44, 28, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 511), (140, 187), (72, 1), (44, 440), (28, 184), (2, 24), (1, 8)]
    (codeMat 142) (codeMat 311) (codeMat 307) false
    det142 det311 inv311
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4384_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 140, 72, 44, 28, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4384_orbit
  simpa only [lower10] using h

theorem space4385_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 68, 38, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 326), (68, 324), (38, 424), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    det92 det468 inv468
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4385_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 38, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4385_orbit
  simpa only [lower10] using h

theorem space4386_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 134, 68, 36, 16, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 219), (134, 228), (68, 82), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 87) (codeMat 172) (codeMat 99) false
    det87 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4386_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 134, 68, 36, 16, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4386_orbit
  simpa only [lower11] using h

theorem space4387_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 134, 64, 36, 20, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 3), (134, 198), (64, 130), (36, 216), (20, 240), (12, 208), (1, 128)]
    (codeMat 85) (codeMat 188) (codeMat 103) false
    det85 det188 inv188
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4387_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 134, 64, 36, 20, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4387_orbit
  simpa only [lower11] using h

theorem space4388_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 66, 32, 22, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 326), (130, 325), (66, 324), (32, 432), (22, 424), (12, 160), (1, 256)]
    (codeMat 92) (codeMat 482) (codeMat 143) false
    det92 det482 inv482
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4388_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 22, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4388_orbit
  simpa only [lower10] using h

theorem space4389_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [262, 134, 64, 36, 20, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(262, 196), (134, 199), (64, 2), (36, 32), (20, 248), (14, 80), (1, 128)]
    (codeMat 92) (codeMat 410) (codeMat 331) false
    det92 det410 inv410
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4389_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 36, 20, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4389_orbit
  simpa only [lower11] using h

theorem space4390_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 69, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 480), (133, 96), (69, 224), (36, 3), (17, 149), (8, 511), (2, 360)]
    (codeMat 299) (codeMat 239) (codeMat 351) false
    det299 det239 inv239
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4390_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4390_orbit
  simpa only [lower14] using h

theorem space4391_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 64, 37, 20, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (133, 148), (64, 1), (37, 138), (20, 235), (8, 8), (3, 511)]
    (codeMat 468) (codeMat 181) (codeMat 423) false
    det468 det181 inv181
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4391_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 37, 20, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4391_orbit
  simpa only [lower14] using h

theorem space4392_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 65, 37, 21, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 139), (133, 119), (65, 130), (37, 136), (21, 392), (8, 128), (3, 360)]
    (codeMat 159) (codeMat 190) (codeMat 355) false
    det159 det190 inv190
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4392_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 37, 21, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4392_orbit
  simpa only [lower14] using h

theorem space4393_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 128, 69, 32, 17, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 70), (128, 3), (69, 71), (32, 432), (17, 280), (13, 440), (3, 256)]
    (codeMat 92) (codeMat 379) (codeMat 247) false
    det92 det379 inv379
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4393_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 32, 17, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4393_orbit
  simpa only [lower10] using h

theorem space4394_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 69, 36, 17, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 252), (132, 278), (69, 483), (36, 256), (17, 232), (13, 480), (3, 360)]
    (codeMat 214) (codeMat 409) (codeMat 473) false
    det214 det409 inv409
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4394_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 69, 36, 17, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4394_orbit
  simpa only [lower14] using h

theorem space4395_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [268, 140, 76, 44, 24, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(268, 349), (140, 93), (76, 89), (44, 341), (24, 5), (3, 2)]
    (codeMat 270) (codeMat 249) (codeMat 425) true
    det270 det249 inv249
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4395_lower : 12 ≤ frozenWangTable.L0 (spanCodes [268, 140, 76, 44, 24, 3]) := by
  have h := frozenWangTable.lower_le_L0 25 space4395_orbit
  simpa only [lower25] using h

theorem space4396_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 65, 37, 21, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (133, 71), (65, 3), (37, 424), (21, 440), (8, 24), (3, 256)]
    (codeMat 85) (codeMat 415) (codeMat 253) false
    det85 det415 inv415
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4396_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 37, 21, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4396_orbit
  simpa only [lower10] using h

theorem space4397_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 132, 68, 36, 16, 12, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 3), (132, 196), (68, 198), (36, 216), (16, 32), (12, 240), (3, 128)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    det84 det236 inv236
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4397_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 36, 16, 12, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4397_orbit
  simpa only [lower11] using h

theorem space4398_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 64, 36, 20, 9, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (133, 68), (64, 3), (36, 16), (20, 416), (9, 24), (2, 256)]
    (codeMat 92) (codeMat 169) (codeMat 225) false
    det92 det169 inv169
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4398_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 36, 20, 9, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4398_orbit
  simpa only [lower10] using h

theorem space4399_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 69, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 105), (132, 284), (69, 97), (37, 361), (17, 149), (8, 360), (2, 511)]
    (codeMat 419) (codeMat 467) (codeMat 339) false
    det419 det467 inv467
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4399_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 69, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4399_orbit
  simpa only [lower14] using h

theorem space4400_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 64, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 97), (133, 284), (64, 8), (36, 360), (20, 362), (8, 1), (2, 511)]
    (codeMat 482) (codeMat 407) (codeMat 405) false
    det482 det407 inv407
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4400_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 64, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4400_orbit
  simpa only [lower14] using h

theorem space4401_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 134, 68, 36, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (134, 70), (68, 324), (36, 8), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    det93 det212 inv212
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4401_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 134, 68, 36, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4401_orbit
  simpa only [lower10] using h

theorem space4402_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 132, 64, 38, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 30), (132, 29), (64, 9), (38, 414), (20, 373), (10, 105), (1, 8)]
    (codeMat 461) (codeMat 419) (codeMat 183) false
    det461 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4402_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 132, 64, 38, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4402_orbit
  simpa only [lower14] using h

theorem space4403_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 130, 68, 32, 16, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (130, 3), (68, 324), (32, 8), (16, 24), (14, 160), (1, 256)]
    (codeMat 85) (codeMat 86) (codeMat 212) false
    det85 det86 inv86
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4403_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 68, 32, 16, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4403_orbit
  simpa only [lower10] using h

theorem space4404_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 128, 70, 34, 18, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 137), (128, 128), (70, 393), (34, 138), (18, 130), (12, 227), (1, 511)]
    (codeMat 279) (codeMat 125) (codeMat 348) false
    det279 det125 inv125
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4404_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 128, 70, 34, 18, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4404_orbit
  simpa only [lower14] using h

theorem space4405_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 130, 68, 32, 16, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 276), (130, 130), (68, 105), (32, 256), (16, 128), (12, 96), (1, 8)]
    (codeMat 143) (codeMat 273) (codeMat 273) false
    det143 det273 inv273
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4405_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 68, 32, 16, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4405_orbit
  simpa only [lower14] using h

theorem space4406_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 134, 64, 36, 20, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 21), (134, 23), (64, 1), (36, 360), (20, 488), (12, 104), (1, 8)]
    (codeMat 140) (codeMat 407) (codeMat 405) false
    det140 det407 inv407
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4406_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 36, 20, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4406_orbit
  simpa only [lower14] using h

theorem space4407_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [268, 128, 64, 32, 20, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(268, 228), (128, 2), (64, 3), (32, 256), (20, 160), (2, 16), (1, 24)]
    (codeMat 140) (codeMat 281) (codeMat 281) false
    det140 det281 inv281
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4407_lower : 12 ≤ frozenWangTable.L0 (spanCodes [268, 128, 64, 32, 20, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4407_orbit
  simpa only [lower10] using h

theorem space4408_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 131, 65, 32, 17, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 208), (131, 112), (65, 8), (32, 2), (17, 70), (8, 1), (4, 128)]
    (codeMat 106) (codeMat 177) (codeMat 417) false
    det106 det177 inv177
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4408_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 17, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space4408_orbit
  simpa only [lower11] using h

theorem space4409_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [266, 137, 72, 42, 25, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(266, 94), (137, 338), (72, 7), (42, 88), (25, 336), (5, 8)]
    (codeMat 206) (codeMat 377) (codeMat 369) false
    det206 det377 inv377
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4409_lower : 12 ≤ frozenWangTable.L0 (spanCodes [266, 137, 72, 42, 25, 5]) := by
  have h := frozenWangTable.lower_le_L0 25 space4409_orbit
  simpa only [lower25] using h

theorem space4410_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 34, 19, 9, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 392), (129, 224), (66, 480), (34, 414), (19, 227), (9, 511), (5, 8)]
    (codeMat 335) (codeMat 379) (codeMat 247) false
    det335 det379 inv379
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4410_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 19, 9, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4410_orbit
  simpa only [lower14] using h

theorem space4411_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 131, 64, 32, 18, 8, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (131, 326), (64, 3), (32, 16), (18, 432), (8, 24), (6, 256)]
    (codeMat 84) (codeMat 185) (codeMat 481) false
    det84 det185 inv185
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4411_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 32, 18, 8, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4411_orbit
  simpa only [lower10] using h

theorem space4412_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 64, 35, 18, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 69), (128, 1), (64, 2), (35, 424), (18, 8), (9, 16), (6, 256)]
    (codeMat 92) (codeMat 270) (codeMat 298) false
    det92 det270 inv270
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4412_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 35, 18, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4412_orbit
  simpa only [lower10] using h

theorem space4413_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 129, 65, 34, 19, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 259), (129, 327), (65, 2), (34, 280), (19, 184), (9, 16), (6, 256)]
    (codeMat 93) (codeMat 190) (codeMat 355) false
    det93 det190 inv190
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4413_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 34, 19, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4413_orbit
  simpa only [lower10] using h

theorem space4414_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 66, 35, 16, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 69), (128, 1), (66, 71), (35, 424), (16, 8), (11, 440), (6, 256)]
    (codeMat 84) (codeMat 335) (codeMat 426) false
    det84 det335 inv335
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4414_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 35, 16, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4414_orbit
  simpa only [lower10] using h

theorem space4415_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 67, 35, 16, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 100), (128, 219), (67, 237), (35, 160), (16, 216), (9, 40), (7, 128)]
    (codeMat 94) (codeMat 339) (codeMat 467) false
    det94 det339 inv339
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4415_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 16, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4415_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
