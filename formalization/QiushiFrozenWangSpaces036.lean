import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1152_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 161, 65, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 502), (161, 372), (65, 1), (17, 96), (8, 8), (4, 384), (2, 256)]
    (codeMat 85) (codeMat 417) (codeMat 177) false
    det85 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1152_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 161, 65, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1152_orbit
  simpa only [lower14] using h

theorem space1153_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 128, 97, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 8), (128, 130), (97, 393), (17, 149), (8, 511), (4, 1), (2, 2)]
    (codeMat 369) (codeMat 93) (codeMat 372) false
    det369 det93 inv93
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1153_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 128, 97, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1153_orbit
  simpa only [lower14] using h

theorem space1154_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 129, 96, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 1), (129, 162), (96, 324), (17, 160), (8, 256), (4, 8), (2, 16)]
    (codeMat 142) (codeMat 84) (codeMat 84) false
    det142 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1154_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 96, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1154_orbit
  simpa only [lower10] using h

theorem space1155_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 128, 96, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 31), (128, 130), (96, 284), (17, 149), (8, 511), (4, 3), (2, 2)]
    (codeMat 369) (codeMat 125) (codeMat 348) false
    det369 det125 inv125
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1155_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 128, 96, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1155_orbit
  simpa only [lower14] using h

theorem space1156_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [260, 130, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(260, 4), (130, 3), (64, 130), (18, 216), (10, 208), (1, 128)]
    (codeMat 85) (codeMat 282) (codeMat 267) false
    det85 det282 inv282
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1156_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1156_orbit
  simpa only [lower23] using h

theorem space1157_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [290, 160, 66, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(290, 387), (160, 414), (66, 21), (18, 360), (10, 151), (6, 3), (1, 2)]
    (codeMat 481) (codeMat 426) (codeMat 335) false
    det481 det426 inv426
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1157_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 160, 66, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1157_orbit
  simpa only [lower14] using h

theorem space1158_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [290, 162, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(290, 503), (162, 502), (64, 2), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 140) (codeMat 444) (codeMat 110) false
    det140 det444 inv444
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1158_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 162, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1158_orbit
  simpa only [lower10] using h

theorem space1159_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 160, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 325), (160, 326), (64, 2), (18, 432), (10, 176), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 412) (codeMat 111) false
    det140 det412 inv412
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1159_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1159_orbit
  simpa only [lower10] using h

theorem space1160_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [288, 160, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(288, 3), (160, 326), (66, 178), (18, 432), (10, 176), (4, 24), (1, 16)]
    (codeMat 142) (codeMat 188) (codeMat 103) false
    det142 det188 inv188
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1160_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 160, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1160_orbit
  simpa only [lower10] using h

theorem space1161_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [288, 130, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(288, 4), (130, 219), (66, 210), (18, 216), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    det86 det282 inv282
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1161_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 130, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 23 space1161_orbit
  simpa only [lower23] using h

theorem space1162_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 132, 66, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 414), (132, 373), (66, 105), (32, 384), (18, 360), (10, 104), (1, 8)]
    (codeMat 142) (codeMat 419) (codeMat 183) false
    det142 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1162_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 132, 66, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1162_orbit
  simpa only [lower14] using h

theorem space1163_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 130, 68, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 126), (130, 9), (68, 245), (32, 384), (18, 8), (10, 264), (1, 360)]
    (codeMat 158) (codeMat 355) (codeMat 190) false
    det158 det355 inv355
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1163_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 68, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1163_orbit
  simpa only [lower14] using h

theorem space1164_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 68, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (132, 70), (68, 68), (32, 8), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    det84 det212 inv212
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1164_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1164_orbit
  simpa only [lower10] using h

theorem space1165_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 128, 70, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 510), (128, 1), (70, 509), (32, 384), (18, 8), (10, 264), (1, 360)]
    (codeMat 156) (codeMat 355) (codeMat 190) false
    det156 det355 inv355
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1165_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 128, 70, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1165_orbit
  simpa only [lower14] using h

theorem space1166_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 134, 70, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (134, 326), (70, 324), (32, 24), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    det84 det244 inv244
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1166_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 134, 70, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1166_orbit
  simpa only [lower10] using h

theorem space1167_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 132, 68, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 105), (132, 97), (68, 227), (34, 361), (18, 360), (10, 362), (1, 511)]
    (codeMat 426) (codeMat 459) (codeMat 346) false
    det426 det459 inv459
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1167_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 132, 68, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1167_orbit
  simpa only [lower14] using h

theorem space1168_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 134, 68, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (134, 326), (68, 68), (34, 424), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 468) (codeMat 87) false
    det85 det468 inv468
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1168_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 134, 68, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1168_orbit
  simpa only [lower10] using h

theorem space1169_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 134, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 235), (134, 414), (70, 284), (34, 363), (18, 360), (10, 362), (1, 511)]
    (codeMat 426) (codeMat 491) (codeMat 375) false
    det426 det491 inv491
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1169_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 134, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1169_orbit
  simpa only [lower14] using h

theorem space1170_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 68, 36, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 2), (68, 68), (36, 8), (18, 16), (10, 416), (1, 256)]
    (codeMat 92) (codeMat 84) (codeMat 84) false
    det92 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1170_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1170_orbit
  simpa only [lower10] using h

theorem space1171_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 68, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 406), (128, 130), (68, 227), (38, 150), (18, 2), (10, 362), (1, 511)]
    (codeMat 491) (codeMat 345) (codeMat 345) false
    det491 det345 inv345
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1171_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 68, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1171_orbit
  simpa only [lower14] using h

theorem space1172_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 130, 68, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (130, 2), (68, 68), (38, 168), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 340) (codeMat 85) false
    det93 det340 inv340
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1172_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 68, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1172_orbit
  simpa only [lower10] using h

theorem space1173_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 70, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 327), (130, 2), (70, 68), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    det93 det372 inv372
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1173_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 70, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1173_orbit
  simpa only [lower10] using h

theorem space1174_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 133, 65, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (133, 324), (65, 2), (32, 24), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    det85 det172 inv172
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1174_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1174_orbit
  simpa only [lower10] using h

theorem space1175_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (128, 2), (64, 1), (33, 112), (17, 80), (8, 8), (2, 128)]
    (codeMat 84) (codeMat 305) (codeMat 305) false
    det84 det305 inv305
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1175_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1175_orbit
  simpa only [lower11] using h

theorem space1176_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (129, 82), (64, 9), (33, 112), (17, 80), (8, 8), (2, 128)]
    (codeMat 86) (codeMat 305) (codeMat 305) false
    det86 det305 inv305
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1176_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1176_orbit
  simpa only [lower11] using h

theorem space1177_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 128, 65, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 196), (128, 130), (65, 3), (36, 32), (17, 80), (8, 216), (2, 128)]
    (codeMat 93) (codeMat 281) (codeMat 281) false
    det93 det281 inv281
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1177_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1177_orbit
  simpa only [lower11] using h

theorem space1178_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 64, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (133, 149), (64, 1), (37, 136), (17, 96), (8, 8), (2, 360)]
    (codeMat 212) (codeMat 167) (codeMat 167) false
    det212 det167 inv167
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1178_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1178_orbit
  simpa only [lower14] using h

theorem space1179_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 133, 69, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 71), (133, 68), (69, 70), (37, 440), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 492) (codeMat 115) false
    det92 det492 inv492
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1179_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1179_orbit
  simpa only [lower10] using h

theorem space1180_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [288, 128, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(288, 4), (128, 9), (65, 219), (16, 8), (9, 216), (3, 128)]
    (codeMat 86) (codeMat 267) (codeMat 282) false
    det86 det267 inv267
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1180_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 128, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 23 space1180_orbit
  simpa only [lower23] using h

theorem space1181_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 196), (128, 1), (64, 3), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    det84 det267 inv267
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1181_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1181_orbit
  simpa only [lower11] using h

theorem space1182_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 126), (133, 252), (65, 9), (32, 384), (16, 256), (9, 8), (3, 360)]
    (codeMat 158) (codeMat 417) (codeMat 177) false
    det158 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1182_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1182_orbit
  simpa only [lower14] using h

theorem space1183_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 129, 68, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (129, 258), (68, 326), (32, 24), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 124) (codeMat 124) false
    det85 det124 inv124
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1183_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1183_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
