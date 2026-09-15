import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4512_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 128, 64, 33, 17, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 224), (128, 128), (64, 256), (33, 508), (17, 148), (5, 3), (2, 2)]
    (codeMat 305) (codeMat 372) (codeMat 93) false
    det305 det372 inv372
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4512_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 128, 64, 33, 17, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4512_orbit
  simpa only [lower14] using h

theorem space4513_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 137, 65, 40, 16, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 256), (137, 246), (65, 432), (40, 2), (16, 3), (5, 16), (2, 24)]
    (codeMat 266) (codeMat 346) (codeMat 459) false
    det266 det346 inv346
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4513_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 137, 65, 40, 16, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4513_orbit
  simpa only [lower10] using h

theorem space4514_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 144, 81, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 259), (144, 8), (81, 393), (49, 362), (8, 511), (5, 3), (2, 1)]
    (codeMat 369) (codeMat 331) (codeMat 410) false
    det369 det331 inv331
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4514_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 81, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4514_orbit
  simpa only [lower14] using h

theorem space4515_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [265, 129, 64, 32, 16, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(265, 228), (129, 160), (64, 256), (32, 3), (16, 2), (4, 24), (2, 16)]
    (codeMat 266) (codeMat 116) (codeMat 92) false
    det266 det116 inv116
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4515_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 129, 64, 32, 16, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4515_orbit
  simpa only [lower10] using h

theorem space4516_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [262, 134, 70, 36, 18, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(262, 100), (134, 109), (70, 82), (36, 32), (18, 40), (14, 208), (1, 128)]
    (codeMat 95) (codeMat 394) (codeMat 330) false
    det95 det394 inv394
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4516_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 70, 36, 18, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4516_orbit
  simpa only [lower11] using h

theorem space4517_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 130, 64, 32, 20, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 28), (130, 3), (64, 9), (32, 256), (20, 224), (12, 96), (1, 8)]
    (codeMat 141) (codeMat 275) (codeMat 275) false
    det141 det275 inv275
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4517_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 64, 32, 20, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4517_orbit
  simpa only [lower14] using h

theorem space4518_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 66, 38, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 360), (132, 353), (66, 278), (38, 105), (22, 97), (10, 276), (1, 130)]
    (codeMat 470) (codeMat 396) (codeMat 106) false
    det470 det396 inv396
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4518_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 66, 38, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4518_orbit
  simpa only [lower14] using h

theorem space4519_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 134, 68, 36, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 8), (134, 392), (68, 96), (36, 1), (16, 511), (10, 149), (1, 360)]
    (codeMat 355) (codeMat 215) (codeMat 342) false
    det355 det215 inv215
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4519_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 134, 68, 36, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4519_orbit
  simpa only [lower14] using h

theorem space4520_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [266, 136, 74, 42, 24, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(266, 206), (136, 191), (74, 21), (42, 248), (24, 128), (6, 8), (1, 40)]
    (codeMat 143) (codeMat 499) (codeMat 382) false
    det143 det499 inv499
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4520_lower : 12 ≤ frozenWangTable.L0 (spanCodes [266, 136, 74, 42, 24, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4520_orbit
  simpa only [lower11] using h

theorem space4521_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [266, 130, 64, 32, 18, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(266, 405), (130, 1), (64, 130), (32, 360), (18, 8), (6, 256), (1, 128)]
    (codeMat 93) (codeMat 270) (codeMat 298) false
    det93 det270 inv270
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4521_lower : 12 ≤ frozenWangTable.L0 (spanCodes [266, 130, 64, 32, 18, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4521_orbit
  simpa only [lower14] using h

theorem space4522_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 146, 82, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 361), (146, 256), (82, 255), (48, 8), (10, 28), (6, 1), (1, 3)]
    (codeMat 465) (codeMat 397) (codeMat 250) false
    det465 det397 inv397
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4522_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 146, 82, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4522_orbit
  simpa only [lower14] using h

theorem space4523_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 136, 64, 42, 16, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (136, 68), (64, 1), (42, 160), (16, 256), (4, 24), (1, 8)]
    (codeMat 140) (codeMat 165) (codeMat 163) false
    det140 det165 inv165
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4523_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 136, 64, 42, 16, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4523_orbit
  simpa only [lower10] using h

theorem space4524_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 138, 64, 40, 16, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 30), (138, 118), (64, 8), (40, 128), (16, 384), (4, 3), (1, 1)]
    (codeMat 161) (codeMat 181) (codeMat 423) false
    det161 det181 inv181
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4524_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 138, 64, 40, 16, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4524_orbit
  simpa only [lower14] using h

theorem space4525_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [274, 130, 80, 32, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(274, 246), (130, 432), (80, 70), (32, 3), (8, 1), (4, 24), (1, 8)]
    (codeMat 266) (codeMat 181) (codeMat 423) false
    det266 det181 inv181
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4525_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 130, 80, 32, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4525_orbit
  simpa only [lower10] using h

theorem space4526_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [264, 128, 64, 32, 20, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(264, 68), (128, 2), (64, 1), (32, 256), (20, 160), (2, 16), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    det140 det273 inv273
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4526_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 128, 64, 32, 20, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4526_orbit
  simpa only [lower10] using h

theorem space4527_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 66, 34, 18, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (128, 3), (66, 196), (34, 208), (18, 216), (8, 32), (4, 128), (1, 256)]
    (codeMat 84) (codeMat 114) (codeMat 204) false
    det84 det114 inv114
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4527_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 18, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4527_orbit
  simpa only [lower3] using h

theorem space4528_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 324), (130, 325), (64, 2), (32, 32), (16, 40), (10, 336), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 394) (codeMat 330) false
    det84 det394 inv394
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4528_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4528_orbit
  simpa only [lower3] using h

theorem space4529_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 66, 34, 16, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (128, 1), (66, 68), (34, 88), (16, 8), (8, 32), (6, 128), (1, 256)]
    (codeMat 84) (codeMat 102) (codeMat 156) false
    det84 det102 inv102
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4529_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4529_orbit
  simpa only [lower3] using h

theorem space4530_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (130, 325), (66, 326), (32, 8), (16, 40), (10, 368), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 206) (codeMat 498) false
    det84 det206 inv206
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4530_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4530_orbit
  simpa only [lower3] using h

theorem space4531_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 33, 17, 9, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 454), (128, 2), (65, 455), (33, 496), (17, 464), (9, 504), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 377) (codeMat 369) false
    det84 det377 inv377
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4531_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 17, 9, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space4531_orbit
  simpa only [lower3] using h

theorem space4532_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 32, 16, 9, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (129, 452), (65, 455), (32, 8), (16, 32), (9, 504), (5, 384), (2, 256)]
    (codeMat 84) (codeMat 205) (codeMat 242) false
    det84 det205 inv205
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4532_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 16, 9, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space4532_orbit
  simpa only [lower3] using h

theorem space4533_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 16, 8, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 69), (64, 1), (33, 80), (16, 40), (8, 8), (4, 128), (3, 256)]
    (codeMat 84) (codeMat 163) (codeMat 165) false
    det84 det163 inv163
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4533_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 8, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space4533_orbit
  simpa only [lower3] using h

theorem space4534_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 33, 17, 8, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 326), (129, 327), (65, 325), (33, 368), (17, 376), (8, 40), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 499) (codeMat 382) false
    det84 det499 inv499
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4534_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 17, 8, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space4534_orbit
  simpa only [lower3] using h

theorem space4535_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 17, 8, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (129, 71), (64, 1), (33, 88), (17, 120), (8, 8), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 183) (codeMat 419) false
    det84 det183 inv183
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4535_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 17, 8, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space4535_orbit
  simpa only [lower3] using h

theorem space4536_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 32, 17, 8, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 324), (128, 3), (65, 325), (32, 32), (17, 344), (8, 40), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 339) (codeMat 467) false
    det84 det339 inv339
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4536_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 17, 8, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space4536_orbit
  simpa only [lower3] using h

theorem space4537_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 32, 16, 9, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 453), (129, 452), (65, 455), (32, 40), (16, 32), (9, 504), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 461) (codeMat 234) false
    det84 det461 inv461
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4537_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 16, 9, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space4537_orbit
  simpa only [lower3] using h

theorem space4538_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 32, 17, 9, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 452), (129, 454), (65, 455), (32, 32), (17, 496), (9, 504), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 473) (codeMat 409) false
    det84 det473 inv473
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4538_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 17, 9, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space4538_orbit
  simpa only [lower3] using h

theorem space4539_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 66, 34, 16, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 71), (128, 1), (66, 68), (34, 120), (16, 8), (8, 32), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    det84 det358 inv358
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4539_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 16, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4539_orbit
  simpa only [lower3] using h

theorem space4540_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 66, 34, 18, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 198), (128, 3), (66, 196), (34, 240), (18, 216), (8, 32), (4, 384), (1, 256)]
    (codeMat 84) (codeMat 370) (codeMat 207) false
    det84 det370 inv370
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4540_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 18, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4540_orbit
  simpa only [lower3] using h

theorem space4541_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (132, 198), (64, 2), (36, 216), (20, 240), (12, 208), (2, 384), (1, 128)]
    (codeMat 84) (codeMat 188) (codeMat 103) false
    det84 det188 inv188
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4541_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4541_orbit
  simpa only [lower3] using h

theorem space4542_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [260, 132, 68, 36, 16, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(260, 455), (132, 452), (68, 454), (36, 504), (16, 32), (12, 496), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 492) (codeMat 115) false
    det84 det492 inv492
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space4542_lower : 9 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 36, 16, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space4542_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
