import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4352_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 80, 32, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 150), (128, 511), (80, 227), (32, 130), (9, 256), (4, 2), (3, 3)]
    (codeMat 241) (codeMat 242) (codeMat 205) false
    det241 det242 inv242
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4352_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 80, 32, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4352_orbit
  simpa only [lower14] using h

theorem space4353_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 145, 81, 48, 9, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 375), (145, 374), (81, 373), (48, 8), (9, 360), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    det84 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4353_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 48, 9, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4353_orbit
  simpa only [lower14] using h

theorem space4354_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 144, 80, 49, 9, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 177), (144, 3), (80, 326), (49, 176), (9, 432), (4, 8), (2, 24)]
    (codeMat 142) (codeMat 94) (codeMat 500) false
    det142 det94 inv94
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4354_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 144, 80, 49, 9, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4354_orbit
  simpa only [lower10] using h

theorem space4355_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 145, 80, 48, 9, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 138), (145, 30), (80, 373), (48, 130), (9, 384), (4, 1), (2, 3)]
    (codeMat 241) (codeMat 94) (codeMat 500) false
    det241 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4355_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 145, 80, 48, 9, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4355_orbit
  simpa only [lower14] using h

theorem space4356_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 146, 82, 48, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 327), (146, 511), (82, 255), (48, 2), (8, 3), (6, 16), (1, 24)]
    (codeMat 266) (codeMat 415) (codeMat 253) false
    det266 det415 inv415
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4356_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 146, 82, 48, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4356_orbit
  simpa only [lower10] using h

theorem space4357_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 80, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 149), (128, 511), (80, 227), (34, 23), (10, 31), (4, 2), (1, 3)]
    (codeMat 465) (codeMat 187) (codeMat 229) false
    det465 det187 inv187
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4357_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 80, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4357_orbit
  simpa only [lower14] using h

theorem space4358_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [274, 144, 80, 50, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(274, 138), (144, 3), (80, 508), (50, 136), (10, 480), (4, 128), (1, 256)]
    (codeMat 94) (codeMat 114) (codeMat 204) false
    det94 det114 inv114
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4358_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 144, 80, 50, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4358_orbit
  simpa only [lower14] using h

theorem space4359_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 80, 32, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 176), (130, 432), (80, 70), (32, 2), (8, 1), (4, 16), (1, 8)]
    (codeMat 266) (codeMat 177) (codeMat 417) false
    det266 det177 inv177
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4359_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 80, 32, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4359_orbit
  simpa only [lower10] using h

theorem space4360_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [274, 146, 80, 48, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(274, 503), (146, 511), (80, 23), (48, 1), (8, 2), (4, 384), (1, 128)]
    (codeMat 98) (codeMat 442) (codeMat 334) false
    det98 det442 inv442
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4360_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 146, 80, 48, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space4360_orbit
  simpa only [lower14] using h

theorem space4361_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 140, 72, 44, 28, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (140, 169), (72, 3), (44, 424), (28, 168), (2, 8), (1, 24)]
    (codeMat 142) (codeMat 271) (codeMat 314) false
    det142 det271 inv271
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4361_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 140, 72, 44, 28, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4361_orbit
  simpa only [lower10] using h

theorem space4362_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [256, 130, 65, 33, 17, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(256, 9), (130, 5), (65, 2), (33, 80), (17, 336), (4, 8)]
    (codeMat 141) (codeMat 142) (codeMat 354) false
    det141 det142 inv142
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4362_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 65, 33, 17, 4]) := by
  have h := frozenWangTable.lower_le_L0 25 space4362_orbit
  simpa only [lower25] using h

theorem space4363_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 34, 18, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (128, 3), (66, 28), (34, 88), (18, 216), (4, 8), (1, 32)]
    (codeMat 140) (codeMat 86) (codeMat 212) false
    det140 det86 inv86
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4363_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 18, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4363_orbit
  simpa only [lower11] using h

theorem space4364_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 34, 16, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 3), (128, 2), (66, 20), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 140) (codeMat 116) (codeMat 92) false
    det140 det116 inv116
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4364_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4364_orbit
  simpa only [lower11] using h

theorem space4365_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [264, 130, 72, 32, 26, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(264, 324), (130, 511), (72, 1), (32, 256), (26, 440), (6, 24), (1, 8)]
    (codeMat 142) (codeMat 403) (codeMat 403) false
    det142 det403 inv403
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4365_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 130, 72, 32, 26, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4365_orbit
  simpa only [lower10] using h

theorem space4366_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 65, 32, 17, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 22), (129, 30), (65, 54), (32, 128), (17, 198), (4, 2), (2, 3)]
    (codeMat 161) (codeMat 122) (codeMat 460) false
    det161 det122 inv122
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4366_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 17, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4366_orbit
  simpa only [lower11] using h

theorem space4367_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 129, 72, 32, 24, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 151), (129, 224), (72, 511), (32, 2), (24, 3), (4, 128), (2, 256)]
    (codeMat 106) (codeMat 233) (codeMat 233) false
    det106 det233 inv233
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4367_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 129, 72, 32, 24, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4367_orbit
  simpa only [lower14] using h

theorem space4368_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 33, 17, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 43), (128, 9), (64, 54), (33, 240), (17, 112), (5, 40), (2, 8)]
    (codeMat 141) (codeMat 110) (codeMat 444) false
    det141 det110 inv110
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4368_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 17, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4368_orbit
  simpa only [lower11] using h

theorem space4369_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [265, 128, 72, 33, 25, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(265, 480), (128, 8), (72, 511), (33, 259), (25, 385), (5, 3), (2, 1)]
    (codeMat 225) (codeMat 331) (codeMat 410) false
    det225 det331 inv331
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4369_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 128, 72, 33, 25, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4369_orbit
  simpa only [lower14] using h

theorem space4370_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 33, 16, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 9), (129, 34), (64, 54), (33, 112), (16, 128), (4, 8), (3, 32)]
    (codeMat 141) (codeMat 92) (codeMat 116) false
    det141 det92 inv92
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4370_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4370_orbit
  simpa only [lower11] using h

theorem space4371_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [264, 136, 65, 40, 17, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(264, 259), (136, 70), (65, 511), (40, 256), (17, 440), (4, 24), (3, 8)]
    (codeMat 142) (codeMat 253) (codeMat 415) false
    det142 det253 inv253
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4371_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 136, 65, 40, 17, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4371_orbit
  simpa only [lower10] using h

theorem space4372_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [265, 128, 72, 32, 24, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(265, 237), (128, 256), (72, 325), (32, 3), (24, 1), (4, 24), (3, 8)]
    (codeMat 266) (codeMat 229) (codeMat 187) false
    det266 det229 inv229
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4372_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 128, 72, 32, 24, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4372_orbit
  simpa only [lower10] using h

theorem space4373_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 136, 73, 40, 24, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 256), (136, 327), (73, 511), (40, 3), (24, 2), (5, 24), (3, 16)]
    (codeMat 266) (codeMat 459) (codeMat 346) false
    det266 det459 inv459
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4373_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 136, 73, 40, 24, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4373_orbit
  simpa only [lower10] using h

theorem space4374_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 129, 72, 33, 25, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 381), (129, 259), (72, 511), (33, 488), (25, 480), (5, 128), (3, 256)]
    (codeMat 85) (codeMat 351) (codeMat 239) false
    det85 det351 inv351
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4374_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 129, 72, 33, 25, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4374_orbit
  simpa only [lower14] using h

theorem space4375_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 136, 72, 40, 25, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 385), (136, 381), (72, 511), (40, 8), (25, 23), (5, 1), (3, 2)]
    (codeMat 337) (codeMat 491) (codeMat 375) false
    det337 det491 inv491
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4375_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 136, 72, 40, 25, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4375_orbit
  simpa only [lower14] using h

theorem space4376_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [264, 137, 65, 42, 18, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(264, 343), (137, 81), (65, 260), (42, 15), (18, 8), (7, 6)]
    (codeMat 355) (codeMat 369) (codeMat 377) true
    det355 det369 inv369
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4376_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 137, 65, 42, 18, 7]) := by
  have h := frozenWangTable.lower_le_L0 25 space4376_orbit
  simpa only [lower25] using h

theorem space4377_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [256, 128, 64, 35, 16, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(256, 1), (128, 4), (64, 6), (35, 80), (16, 256), (4, 8)]
    (codeMat 140) (codeMat 204) (codeMat 114) false
    det140 det204 inv204
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4377_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 64, 35, 16, 4]) := by
  have h := frozenWangTable.lower_le_L0 25 space4377_orbit
  simpa only [lower25] using h

theorem space4378_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 136, 73, 40, 24, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 440), (136, 327), (73, 511), (40, 1), (24, 2), (5, 8), (3, 16)]
    (codeMat 266) (codeMat 491) (codeMat 375) false
    det266 det491 inv491
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4378_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 136, 73, 40, 24, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4378_orbit
  simpa only [lower10] using h

theorem space4379_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 137, 73, 41, 25, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (137, 509), (73, 511), (41, 440), (25, 184), (4, 8), (3, 16)]
    (codeMat 140) (codeMat 207) (codeMat 370) false
    det140 det207 inv207
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4379_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 137, 73, 41, 25, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4379_orbit
  simpa only [lower10] using h

theorem space4380_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [265, 128, 73, 33, 24, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(265, 510), (128, 3), (73, 511), (33, 440), (24, 256), (5, 8), (2, 24)]
    (codeMat 140) (codeMat 379) (codeMat 247) false
    det140 det379 inv379
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4380_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 128, 73, 33, 24, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4380_orbit
  simpa only [lower10] using h

theorem space4381_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 65, 33, 17, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 30), (128, 8), (65, 54), (33, 198), (17, 70), (4, 3), (2, 1)]
    (codeMat 161) (codeMat 110) (codeMat 444) false
    det161 det110 inv110
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4381_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 17, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4381_orbit
  simpa only [lower11] using h

theorem space4382_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 137, 72, 40, 24, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 224), (137, 119), (72, 511), (40, 3), (24, 1), (4, 256), (2, 384)]
    (codeMat 106) (codeMat 473) (codeMat 409) false
    det106 det473 inv473
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4382_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 137, 72, 40, 24, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4382_orbit
  simpa only [lower14] using h

theorem space4383_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [266, 138, 64, 40, 18, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(266, 247), (138, 246), (64, 3), (40, 256), (18, 432), (6, 8), (1, 24)]
    (codeMat 140) (codeMat 445) (codeMat 478) false
    det140 det445 inv445
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4383_lower : 12 ≤ frozenWangTable.L0 (spanCodes [266, 138, 64, 40, 18, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space4383_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
