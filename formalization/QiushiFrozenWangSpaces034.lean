import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1088_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 100), (131, 457), (67, 502), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 86) (codeMat 330) (codeMat 394) false
    det86 det330 inv330
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1088_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1088_orbit
  simpa only [lower17] using h

theorem space1089_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 429), (129, 457), (64, 63), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 95) (codeMat 335) (codeMat 426) false
    det95 det335 inv335
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1089_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1089_orbit
  simpa only [lower17] using h

theorem space1090_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [290, 129, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(290, 33), (129, 274), (64, 438), (19, 306), (10, 404), (4, 45)]
    (codeMat 382) (codeMat 460) (codeMat 122) false
    det382 det460 inv460
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1090_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 129, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1090_orbit
  simpa only [lower55] using h

theorem space1091_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 274), (130, 63), (67, 502), (35, 208), (19, 440), (10, 112), (4, 128)]
    (codeMat 94) (codeMat 250) (codeMat 397) false
    det94 det250 inv250
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1091_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1091_orbit
  simpa only [lower17] using h

theorem space1092_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 274), (131, 502), (65, 63), (35, 80), (19, 112), (10, 440), (4, 128)]
    (codeMat 87) (codeMat 249) (codeMat 425) false
    det87 det249 inv249
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1092_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1092_orbit
  simpa only [lower17] using h

theorem space1093_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 193, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (193, 139), (34, 132), (19, 404), (10, 306), (4, 2)]
    (codeMat 205) (codeMat 206) (codeMat 498) true
    det205 det206 inv206
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1093_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 193, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1093_orbit
  simpa only [lower55] using h

theorem space1094_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 402), (131, 457), (67, 502), (34, 80), (19, 456), (10, 112), (4, 128)]
    (codeMat 86) (codeMat 106) (codeMat 396) false
    det86 det106 inv106
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1094_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1094_orbit
  simpa only [lower17] using h

theorem space1095_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 322), (130, 1), (66, 391), (34, 208), (19, 456), (10, 440), (4, 128)]
    (codeMat 93) (codeMat 107) (codeMat 428) false
    det93 det107 inv107
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1095_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1095_orbit
  simpa only [lower17] using h

theorem space1096_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 131, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 274), (131, 457), (65, 63), (34, 208), (19, 456), (10, 440), (4, 128)]
    (codeMat 94) (codeMat 107) (codeMat 428) false
    det94 det107 inv107
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1096_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1096_orbit
  simpa only [lower17] using h

theorem space1097_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 322), (130, 1), (64, 390), (34, 80), (19, 456), (10, 112), (4, 128)]
    (codeMat 85) (codeMat 106) (codeMat 396) false
    det85 det106 inv106
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1097_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1097_orbit
  simpa only [lower17] using h

theorem space1098_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 322), (129, 391), (65, 1), (33, 80), (19, 440), (10, 456), (4, 128)]
    (codeMat 85) (codeMat 179) (codeMat 421) false
    det85 det179 inv179
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1098_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1098_orbit
  simpa only [lower17] using h

theorem space1099_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 437), (64, 45), (33, 274), (19, 166), (10, 404), (4, 438)]
    (codeMat 158) (codeMat 445) (codeMat 478) true
    det158 det445 inv445
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1099_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1099_orbit
  simpa only [lower55] using h

theorem space1100_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (32, 1), (18, 216), (10, 208), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 212) (codeMat 86) true
    det266 det212 inv212
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1100_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1100_orbit
  simpa only [lower23] using h

theorem space1101_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (32, 1), (17, 80), (8, 8), (4, 2), (2, 128)]
    (codeMat 266) (codeMat 140) (codeMat 98) true
    det266 det140 inv140
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1101_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1101_orbit
  simpa only [lower23] using h

theorem space1102_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [256, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(256, 4), (32, 1), (16, 8), (9, 216), (4, 2), (3, 128)]
    (codeMat 266) (codeMat 92) (codeMat 116) true
    det266 det92 inv92
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1102_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1102_orbit
  simpa only [lower23] using h

theorem space1103_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 64, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 198), (64, 128), (34, 30), (18, 54), (10, 22), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 188) (codeMat 103) false
    det273 det188 inv188
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1103_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1103_orbit
  simpa only [lower11] using h

theorem space1104_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 64, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 208), (64, 128), (32, 3), (17, 20), (8, 2), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 172) (codeMat 99) false
    det266 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1104_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 64, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1104_orbit
  simpa only [lower11] using h

theorem space1105_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 65, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (65, 216), (32, 2), (17, 28), (8, 3), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 169) (codeMat 225) false
    det266 det169 inv169
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1105_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 65, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1105_orbit
  simpa only [lower11] using h

theorem space1106_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 64, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 80), (64, 128), (32, 9), (16, 54), (9, 2), (4, 8), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    det267 det156 inv156
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1106_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 64, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1106_orbit
  simpa only [lower11] using h

theorem space1107_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 64, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 208), (64, 128), (33, 11), (16, 54), (9, 2), (5, 8), (3, 32)]
    (codeMat 267) (codeMat 188) (codeMat 103) false
    det267 det188 inv188
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1107_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 64, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1107_orbit
  simpa only [lower11] using h

theorem space1108_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 65, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (65, 216), (33, 10), (16, 54), (9, 3), (5, 8), (3, 40)]
    (codeMat 267) (codeMat 185) (codeMat 481) false
    det267 det185 inv185
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1108_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 65, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1108_orbit
  simpa only [lower11] using h

theorem space1109_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [320, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(320, 4), (33, 218), (16, 8), (9, 219), (5, 2), (3, 130)]
    (codeMat 266) (codeMat 377) (codeMat 369) true
    det266 det377 inv377
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1109_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1109_orbit
  simpa only [lower23] using h

theorem space1110_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 65, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 88), (65, 216), (32, 9), (16, 54), (9, 3), (4, 8), (3, 40)]
    (codeMat 267) (codeMat 157) (codeMat 486) false
    det267 det157 inv157
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1110_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 65, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1110_orbit
  simpa only [lower11] using h

theorem space1111_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [320, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(320, 4), (32, 8), (17, 82), (8, 9), (5, 2), (2, 128)]
    (codeMat 266) (codeMat 169) (codeMat 225) true
    det266 det169 inv169
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1111_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1111_orbit
  simpa only [lower23] using h

theorem space1112_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 64, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 80), (64, 128), (32, 1), (17, 20), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1112_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 64, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1112_orbit
  simpa only [lower11] using h

theorem space1113_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [320, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(320, 4), (34, 208), (18, 216), (10, 209), (4, 128), (1, 130)]
    (codeMat 266) (codeMat 465) (codeMat 465) true
    det266 det465 inv465
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1113_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1113_orbit
  simpa only [lower23] using h

theorem space1114_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 88), (130, 216), (32, 9), (18, 3), (10, 60), (4, 8), (1, 32)]
    (codeMat 267) (codeMat 86) (codeMat 212) false
    det267 det86 inv86
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1114_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1114_orbit
  simpa only [lower11] using h

theorem space1115_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [322, 192, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(322, 120), (192, 128), (34, 60), (18, 63), (10, 61), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 467) (codeMat 339) false
    det266 det467 inv467
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1115_lower : 12 ≤ frozenWangTable.L0 (spanCodes [322, 192, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1115_orbit
  simpa only [lower11] using h

theorem space1116_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [384, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(384, 4), (34, 218), (18, 219), (10, 210), (6, 2), (1, 128)]
    (codeMat 266) (codeMat 498) (codeMat 206) true
    det266 det498 inv498
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1116_lower : 12 ≤ frozenWangTable.L0 (spanCodes [384, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1116_orbit
  simpa only [lower23] using h

theorem space1117_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 68), (129, 196), (32, 8), (17, 28), (8, 32), (4, 1), (2, 3)]
    (codeMat 273) (codeMat 86) (codeMat 212) false
    det273 det86 inv86
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1117_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1117_orbit
  simpa only [lower11] using h

theorem space1118_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 196), (128, 128), (33, 28), (17, 20), (8, 32), (4, 3), (2, 2)]
    (codeMat 273) (codeMat 116) (codeMat 92) false
    det273 det116 inv116
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1118_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1118_orbit
  simpa only [lower11] using h

theorem space1119_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [384, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(384, 4), (32, 8), (16, 9), (9, 216), (5, 128), (3, 130)]
    (codeMat 266) (codeMat 122) (codeMat 460) true
    det266 det122 inv122
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1119_lower : 12 ≤ frozenWangTable.L0 (spanCodes [384, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1119_orbit
  simpa only [lower23] using h


end QiushiMatmul.FrozenWang
