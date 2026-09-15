import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1120_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 192, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 71), (192, 128), (33, 55), (16, 40), (9, 63), (5, 1), (3, 2)]
    (codeMat 273) (codeMat 491) (codeMat 375) false
    det273 det491 inv491
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1120_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 192, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1120_orbit
  simpa only [lower11] using h

theorem space1121_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 193, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 71), (193, 199), (33, 55), (16, 32), (9, 63), (5, 1), (3, 3)]
    (codeMat 273) (codeMat 489) (codeMat 241) false
    det273 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1121_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 193, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1121_orbit
  simpa only [lower11] using h

theorem space1122_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 112), (129, 240), (32, 1), (16, 3), (9, 54), (4, 8), (3, 40)]
    (codeMat 266) (codeMat 94) (codeMat 500) false
    det266 det94 inv94
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1122_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1122_orbit
  simpa only [lower11] using h

theorem space1123_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 193, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 120), (193, 248), (32, 54), (17, 28), (8, 63), (5, 8), (2, 32)]
    (codeMat 267) (codeMat 489) (codeMat 241) false
    det267 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1123_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 193, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1123_orbit
  simpa only [lower11] using h

theorem space1124_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [384, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(384, 4), (33, 80), (17, 81), (8, 8), (4, 128), (2, 130)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    det266 det394 inv394
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1124_lower : 12 ≤ frozenWangTable.L0 (spanCodes [384, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1124_orbit
  simpa only [lower23] using h

theorem space1125_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 68), (128, 128), (32, 8), (17, 20), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    det273 det84 inv84
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1125_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1125_orbit
  simpa only [lower11] using h

theorem space1126_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (130, 216), (34, 10), (18, 3), (10, 60), (6, 8), (1, 32)]
    (codeMat 267) (codeMat 114) (codeMat 204) false
    det267 det114 inv114
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1126_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1126_orbit
  simpa only [lower11] using h

theorem space1127_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 208), (128, 128), (34, 11), (18, 2), (10, 52), (6, 8), (1, 32)]
    (codeMat 267) (codeMat 116) (codeMat 92) false
    det267 det116 inv116
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1127_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1127_orbit
  simpa only [lower11] using h

theorem space1128_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [320, 194, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(320, 128), (194, 248), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    det266 det498 inv498
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1128_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 194, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1128_orbit
  simpa only [lower11] using h

theorem space1129_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [322, 192, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(322, 248), (192, 128), (34, 62), (18, 63), (10, 61), (6, 8), (1, 40)]
    (codeMat 266) (codeMat 499) (codeMat 382) false
    det266 det499 inv499
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1129_lower : 12 ≤ frozenWangTable.L0 (spanCodes [322, 192, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1129_orbit
  simpa only [lower11] using h

theorem space1130_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [322, 194, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(322, 112), (194, 240), (34, 52), (18, 54), (10, 53), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 465) (codeMat 465) false
    det266 det465 inv465
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1130_lower : 12 ≤ frozenWangTable.L0 (spanCodes [322, 194, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1130_orbit
  simpa only [lower11] using h

theorem space1131_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 80), (128, 128), (32, 9), (18, 2), (10, 52), (4, 8), (1, 32)]
    (codeMat 267) (codeMat 84) (codeMat 84) false
    det267 det84 inv84
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1131_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1131_orbit
  simpa only [lower11] using h

theorem space1132_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 128, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (128, 3), (64, 2), (18, 216), (10, 208), (1, 128)]
    (codeMat 84) (codeMat 282) (codeMat 267) false
    det84 det282 inv282
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1132_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1132_orbit
  simpa only [lower23] using h

theorem space1133_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 128, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (128, 2), (64, 1), (17, 80), (8, 8), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    det84 det273 inv273
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1133_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1133_orbit
  simpa only [lower23] using h

theorem space1134_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 128, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (128, 1), (64, 3), (16, 8), (9, 216), (3, 128)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    det84 det267 inv267
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1134_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1134_orbit
  simpa only [lower23] using h

theorem space1135_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 160, 64, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 8), (160, 392), (64, 128), (18, 511), (10, 151), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 158) (codeMat 358) false
    det305 det158 inv158
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1135_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 64, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1135_orbit
  simpa only [lower14] using h

theorem space1136_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 162, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 1), (162, 502), (66, 178), (18, 432), (10, 176), (4, 8), (1, 16)]
    (codeMat 142) (codeMat 156) (codeMat 102) false
    det142 det156 inv156
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1136_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 162, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1136_orbit
  simpa only [lower10] using h

theorem space1137_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [290, 128, 98, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(290, 502), (128, 1), (98, 500), (18, 8), (10, 352), (4, 384), (1, 256)]
    (codeMat 92) (codeMat 354) (codeMat 142) false
    det92 det354 inv354
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1137_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 128, 98, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1137_orbit
  simpa only [lower14] using h

theorem space1138_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 162, 96, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (162, 21), (96, 284), (18, 360), (10, 352), (6, 128), (1, 256)]
    (codeMat 87) (codeMat 486) (codeMat 157) false
    det87 det486 inv486
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1138_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 162, 96, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1138_orbit
  simpa only [lower14] using h

theorem space1139_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 161, 65, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 130), (161, 372), (65, 9), (17, 96), (8, 8), (4, 128), (2, 256)]
    (codeMat 87) (codeMat 161) (codeMat 161) false
    det87 det161 inv161
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1139_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 161, 65, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1139_orbit
  simpa only [lower14] using h

theorem space1140_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 129, 97, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 3), (129, 162), (97, 484), (17, 160), (8, 256), (4, 24), (2, 16)]
    (codeMat 142) (codeMat 116) (codeMat 92) false
    det142 det116 inv116
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1140_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 97, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1140_orbit
  simpa only [lower10] using h

theorem space1141_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 22), (128, 1), (64, 2), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 140) (codeMat 298) (codeMat 270) false
    det140 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1141_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1141_orbit
  simpa only [lower11] using h

theorem space1142_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 161, 65, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 131), (161, 380), (65, 9), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 87) (codeMat 165) (codeMat 163) false
    det87 det165 inv165
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1142_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 161, 65, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1142_orbit
  simpa only [lower14] using h

theorem space1143_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 161, 96, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 503), (161, 244), (96, 70), (16, 256), (9, 432), (5, 8), (3, 16)]
    (codeMat 142) (codeMat 492) (codeMat 115) false
    det142 det492 inv492
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1143_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 161, 96, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1143_orbit
  simpa only [lower10] using h

theorem space1144_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [260, 129, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(260, 4), (129, 129), (65, 3), (16, 8), (9, 216), (3, 128)]
    (codeMat 85) (codeMat 267) (codeMat 282) false
    det85 det267 inv267
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1144_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1144_orbit
  simpa only [lower23] using h

theorem space1145_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 160, 97, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (160, 68), (97, 246), (16, 256), (9, 432), (5, 24), (3, 16)]
    (codeMat 142) (codeMat 460) (codeMat 122) false
    det142 det460 inv460
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1145_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 97, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1145_orbit
  simpa only [lower10] using h

theorem space1146_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 161, 97, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (161, 244), (97, 246), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 140) (codeMat 236) (codeMat 123) false
    det140 det236 inv236
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1146_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 161, 97, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1146_orbit
  simpa only [lower10] using h

theorem space1147_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 160, 96, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (160, 68), (96, 70), (16, 256), (9, 432), (4, 8), (3, 16)]
    (codeMat 140) (codeMat 204) (codeMat 114) false
    det140 det204 inv204
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1147_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 96, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1147_orbit
  simpa only [lower10] using h

theorem space1148_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [260, 128, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(260, 4), (128, 130), (65, 1), (17, 80), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    det85 det273 inv273
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1148_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1148_orbit
  simpa only [lower23] using h

theorem space1149_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 129, 97, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 384), (129, 21), (97, 413), (17, 149), (8, 360), (5, 3), (2, 2)]
    (codeMat 417) (codeMat 369) (codeMat 377) false
    det417 det369 inv369
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1149_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 97, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1149_orbit
  simpa only [lower14] using h

theorem space1150_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [289, 128, 97, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(289, 487), (128, 2), (97, 484), (17, 160), (8, 256), (5, 24), (2, 16)]
    (codeMat 140) (codeMat 372) (codeMat 93) false
    det140 det372 inv372
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1150_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 128, 97, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1150_orbit
  simpa only [lower10] using h

theorem space1151_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 128, 96, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 325), (128, 2), (96, 324), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 140) (codeMat 340) (codeMat 85) false
    det140 det340 inv340
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1151_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 128, 96, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1151_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
