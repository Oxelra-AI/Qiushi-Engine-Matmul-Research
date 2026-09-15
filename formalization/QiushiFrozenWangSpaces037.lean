import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1184_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 68, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 30), (132, 20), (68, 29), (32, 384), (16, 256), (9, 360), (3, 8)]
    (codeMat 141) (codeMat 481) (codeMat 185) false
    det141 det481 inv481
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1184_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1184_orbit
  simpa only [lower14] using h

theorem space1185_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 69, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 8), (128, 130), (69, 97), (32, 1), (16, 2), (9, 360), (3, 511)]
    (codeMat 426) (codeMat 85) (codeMat 340) false
    det426 det85 inv85
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1185_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 69, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1185_orbit
  simpa only [lower14] using h

theorem space1186_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 128, 68, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (128, 2), (68, 326), (33, 424), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 348) (codeMat 125) false
    det84 det348 inv348
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1186_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1186_orbit
  simpa only [lower10] using h

theorem space1187_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 128, 69, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 71), (128, 2), (69, 70), (33, 440), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 380) (codeMat 117) false
    det84 det380 inv380
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1187_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1187_orbit
  simpa only [lower10] using h

theorem space1188_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 64, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (133, 70), (64, 2), (36, 24), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 188) (codeMat 103) false
    det92 det188 inv188
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1188_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1188_orbit
  simpa only [lower10] using h

theorem space1189_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (132, 224), (64, 128), (37, 148), (16, 511), (9, 2), (3, 360)]
    (codeMat 299) (codeMat 410) (codeMat 331) false
    det299 det410 inv410
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1189_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1189_orbit
  simpa only [lower14] using h

theorem space1190_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 132, 65, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 327), (132, 70), (65, 2), (37, 184), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 444) (codeMat 110) false
    det93 det444 inv444
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1190_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 65, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1190_orbit
  simpa only [lower10] using h

theorem space1191_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 65, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (133, 70), (65, 2), (37, 168), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 412) (codeMat 111) false
    det93 det412 inv412
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1191_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1191_orbit
  simpa only [lower10] using h

theorem space1192_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 198), (128, 1), (64, 3), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 84) (codeMat 299) (codeMat 318) false
    det84 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1192_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1192_orbit
  simpa only [lower11] using h

theorem space1193_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 69, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (132, 284), (69, 381), (33, 488), (16, 256), (9, 360), (3, 8)]
    (codeMat 143) (codeMat 485) (codeMat 171) false
    det143 det485 inv485
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1193_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 69, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1193_orbit
  simpa only [lower14] using h

theorem space1194_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 65, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 228), (128, 9), (65, 219), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 86) (codeMat 267) (codeMat 282) false
    det86 det267 inv267
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1194_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1194_orbit
  simpa only [lower11] using h

theorem space1195_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 133, 65, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (133, 508), (65, 1), (32, 128), (16, 256), (9, 8), (3, 360)]
    (codeMat 157) (codeMat 161) (codeMat 161) false
    det157 det161 inv161
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1195_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1195_orbit
  simpa only [lower14] using h

theorem space1196_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 129, 69, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (129, 258), (69, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 92) (codeMat 116) false
    det85 det92 inv92
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1196_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 69, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1196_orbit
  simpa only [lower10] using h

theorem space1197_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 129, 65, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 70), (129, 131), (65, 1), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 93) (codeMat 307) (codeMat 311) false
    det93 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1197_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1197_orbit
  simpa only [lower11] using h

theorem space1198_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (133, 224), (64, 128), (37, 150), (16, 511), (9, 2), (3, 360)]
    (codeMat 299) (codeMat 442) (codeMat 334) false
    det299 det442 inv442
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1198_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1198_orbit
  simpa only [lower14] using h

theorem space1199_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 406), (132, 97), (64, 130), (37, 150), (16, 360), (9, 2), (3, 511)]
    (codeMat 491) (codeMat 394) (codeMat 330) false
    det491 det394 inv394
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1199_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1199_orbit
  simpa only [lower14] using h

theorem space1200_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 64, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (132, 70), (64, 2), (36, 8), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 156) (codeMat 102) false
    det92 det156 inv156
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1200_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1200_orbit
  simpa only [lower10] using h

theorem space1201_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 133, 69, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (133, 29), (69, 20), (36, 128), (16, 360), (9, 256), (3, 8)]
    (codeMat 205) (codeMat 226) (codeMat 141) false
    det205 det226 inv226
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1201_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 69, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1201_orbit
  simpa only [lower14] using h

theorem space1202_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 69, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 406), (132, 373), (69, 276), (36, 384), (16, 360), (9, 256), (3, 8)]
    (codeMat 207) (codeMat 482) (codeMat 143) false
    det207 det482 inv482
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1202_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 69, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1202_orbit
  simpa only [lower14] using h

theorem space1203_orbit :
    frozenWangTable.OrbitImage 23 (spanCodes [288, 129, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 23 [(288, 4), (129, 82), (64, 9), (17, 80), (8, 8), (2, 128)]
    (codeMat 86) (codeMat 273) (codeMat 273) false
    det86 det273 inv273
    (by rw [basis23]; decide +kernel)
    (by rw [basis23]; decide +kernel)

theorem space1203_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 129, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 23 space1203_orbit
  simpa only [lower23] using h

theorem space1204_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 65, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 406), (132, 284), (65, 130), (33, 150), (17, 149), (8, 2), (2, 511)]
    (codeMat 482) (codeMat 410) (codeMat 331) false
    det482 det410 inv410
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1204_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 65, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1204_orbit
  simpa only [lower14] using h

theorem space1205_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 133, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 327), (133, 324), (64, 2), (33, 184), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 428) (codeMat 107) false
    det84 det428 inv428
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1205_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1205_orbit
  simpa only [lower10] using h

theorem space1206_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 64, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 324), (64, 2), (33, 168), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    det84 det396 inv396
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1206_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1206_orbit
  simpa only [lower10] using h

theorem space1207_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 128, 69, 33, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 31), (128, 1), (69, 28), (33, 480), (17, 96), (8, 256), (2, 8)]
    (codeMat 140) (codeMat 358) (codeMat 158) false
    det140 det358 inv358
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1207_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 33, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1207_orbit
  simpa only [lower14] using h

theorem space1208_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 65, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (132, 324), (65, 2), (32, 8), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 140) (codeMat 98) false
    det85 det140 inv140
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1208_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1208_orbit
  simpa only [lower10] using h

theorem space1209_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 32, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 68), (128, 2), (64, 1), (32, 32), (17, 80), (8, 8), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    det84 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1209_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1209_orbit
  simpa only [lower11] using h

theorem space1210_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 128, 65, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 198), (128, 130), (65, 3), (37, 240), (17, 80), (8, 216), (2, 128)]
    (codeMat 93) (codeMat 313) (codeMat 313) false
    det93 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1210_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1210_orbit
  simpa only [lower11] using h

theorem space1211_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 68, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (128, 1), (68, 29), (37, 232), (17, 96), (8, 360), (2, 8)]
    (codeMat 204) (codeMat 103) (codeMat 188) false
    det204 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1211_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1211_orbit
  simpa only [lower14] using h

theorem space1212_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 68, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 235), (133, 227), (68, 414), (37, 363), (17, 149), (8, 360), (2, 511)]
    (codeMat 419) (codeMat 499) (codeMat 382) false
    det419 det499 inv499
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1212_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 68, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1212_orbit
  simpa only [lower14] using h

theorem space1213_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 68, 37, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 324), (68, 326), (37, 424), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 460) (codeMat 122) false
    det92 det460 inv460
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1213_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 37, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1213_orbit
  simpa only [lower10] using h

theorem space1214_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 69, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (132, 324), (69, 70), (36, 8), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 204) (codeMat 114) false
    det93 det204 inv204
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1214_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1214_orbit
  simpa only [lower10] using h

theorem space1215_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 133, 68, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (133, 68), (68, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    det93 det236 inv236
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1215_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1215_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
