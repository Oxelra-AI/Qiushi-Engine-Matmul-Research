import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3200_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [257, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(257, 258), (9, 16), (3, 1)]
    (codeMat 281) (codeMat 282) (codeMat 267) false
    det281 det282 inv282
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3200_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 433 space3200_orbit
  simpa only [lower433] using h

theorem space3201_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [258, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(258, 17), (10, 259), (6, 1)]
    (codeMat 169) (codeMat 114) (codeMat 204) false
    det169 det114 inv114
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3201_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 433 space3201_orbit
  simpa only [lower433] using h

theorem space3202_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [258, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(258, 274), (18, 16), (10, 17)]
    (codeMat 282) (codeMat 281) (codeMat 281) false
    det282 det281 inv281
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3202_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space3202_orbit
  simpa only [lower433] using h

theorem space3203_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [257, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(257, 280), (16, 1), (9, 27), (3, 16)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    det266 det267 inv267
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3203_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 282 space3203_orbit
  simpa only [lower282] using h

theorem space3204_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 280), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    det266 det282 inv282
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3204_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 282 space3204_orbit
  simpa only [lower282] using h

theorem space3205_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [258, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(258, 274), (34, 258), (10, 259)]
    (codeMat 114) (codeMat 169) (codeMat 225) false
    det114 det169 inv169
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3205_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space3205_orbit
  simpa only [lower433] using h

theorem space3206_orbit :
    frozenWangTable.OrbitImage 437 (spanCodes [258, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 437 [(258, 20), (48, 1), (10, 100)]
    (codeMat 106) (codeMat 114) (codeMat 204) true
    det106 det114 inv114
    (by rw [basis437]; decide +kernel)
    (by rw [basis437]; decide +kernel)

theorem space3206_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 437 space3206_orbit
  simpa only [lower437] using h

theorem space3207_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [258, 66, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(258, 259), (66, 258), (10, 274)]
    (codeMat 116) (codeMat 172) (codeMat 99) false
    det116 det172 inv172
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3207_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 66, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space3207_orbit
  simpa only [lower433] using h

theorem space3208_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 64, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 259), (64, 1), (34, 280), (10, 264)]
    (codeMat 84) (codeMat 165) (codeMat 163) false
    det84 det165 inv165
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3208_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 282 space3208_orbit
  simpa only [lower282] using h

theorem space3209_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 66, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 258), (66, 259), (32, 16), (10, 280)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    det84 det169 inv169
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3209_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 66, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 282 space3209_orbit
  simpa only [lower282] using h

theorem space3210_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [258, 130, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(258, 17), (130, 16), (10, 274)]
    (codeMat 172) (codeMat 116) (codeMat 92) false
    det172 det116 inv116
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space3210_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 130, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space3210_orbit
  simpa only [lower433] using h

theorem space3211_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 128, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 11), (128, 1), (10, 264), (6, 16)]
    (codeMat 140) (codeMat 102) (codeMat 156) false
    det140 det102 inv102
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3211_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 128, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 282 space3211_orbit
  simpa only [lower282] using h

theorem space3212_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 130, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 26), (130, 27), (10, 280), (4, 16)]
    (codeMat 140) (codeMat 114) (codeMat 204) false
    det140 det114 inv114
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space3212_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 130, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 282 space3212_orbit
  simpa only [lower282] using h

theorem space3213_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [258, 34, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(258, 427), (34, 43), (23, 33), (10, 42)]
    (codeMat 410) (codeMat 491) (codeMat 375) false
    det410 det491 inv491
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3213_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 34, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3213_orbit
  simpa only [lower298] using h

theorem space3214_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [258, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(258, 385), (51, 11), (10, 42), (6, 1)]
    (codeMat 345) (codeMat 499) (codeMat 382) false
    det345 det499 inv499
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3214_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 298 space3214_orbit
  simpa only [lower298] using h

theorem space3215_orbit :
    frozenWangTable.OrbitImage 156 (spanCodes [258, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 156 [(258, 112), (35, 33), (19, 30), (10, 43), (7, 32)]
    (codeMat 267) (codeMat 157) (codeMat 486) false
    det267 det157 inv157
    (by rw [basis156]; decide +kernel)
    (by rw [basis156]; decide +kernel)

theorem space3215_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 156 space3215_orbit
  simpa only [lower156] using h

theorem space3216_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [257, 101, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(257, 43), (101, 10), (9, 1), (3, 384)]
    (codeMat 499) (codeMat 167) (codeMat 167) true
    det499 det167 inv167
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3216_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 101, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 298 space3216_orbit
  simpa only [lower298] using h

theorem space3217_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [258, 180, 101, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(258, 97), (180, 96), (101, 368), (10, 274)]
    (codeMat 239) (codeMat 460) (codeMat 122) false
    det239 det460 inv460
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3217_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 180, 101, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3217_orbit
  simpa only [lower276] using h

theorem space3218_orbit :
    frozenWangTable.OrbitImage 156 (spanCodes [258, 129, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 156 [(258, 101), (129, 33), (65, 32), (19, 30), (10, 53)]
    (codeMat 372) (codeMat 314) (codeMat 271) true
    det372 det314 inv314
    (by rw [basis156]; decide +kernel)
    (by rw [basis156]; decide +kernel)

theorem space3218_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 156 space3218_orbit
  simpa only [lower156] using h

theorem space3219_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [258, 149, 86, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(258, 196), (149, 191), (86, 190), (39, 96), (10, 112)]
    (codeMat 93) (codeMat 474) (codeMat 395) false
    det93 det474 inv474
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space3219_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 149, 86, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space3219_orbit
  simpa only [lower152] using h

theorem space3220_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [258, 197, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(258, 97), (197, 96), (53, 272), (10, 274)]
    (codeMat 93) (codeMat 415) (codeMat 253) true
    det93 det415 inv415
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3220_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 197, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3220_orbit
  simpa only [lower276] using h

theorem space3221_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 146, 101, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 306), (146, 2), (101, 97), (10, 338)]
    (codeMat 183) (codeMat 337) (codeMat 337) false
    det183 det337 inv337
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3221_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 146, 101, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3221_orbit
  simpa only [lower278] using h

theorem space3222_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 180, 67, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 96), (180, 97), (67, 336), (10, 338)]
    (codeMat 111) (codeMat 394) (codeMat 330) false
    det111 det394 inv394
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3222_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 180, 67, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3222_orbit
  simpa only [lower278] using h

theorem space3223_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 194, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 306), (194, 304), (53, 97), (10, 96)]
    (codeMat 99) (codeMat 244) (codeMat 95) true
    det99 det244 inv244
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3223_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 194, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3223_orbit
  simpa only [lower278] using h

theorem space3224_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 197, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 96), (197, 97), (50, 304), (10, 306)]
    (codeMat 85) (codeMat 409) (codeMat 473) true
    det85 det409 inv409
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3224_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 197, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3224_orbit
  simpa only [lower278] using h

theorem space3225_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 209, 38, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 338), (209, 97), (38, 336), (10, 96)]
    (codeMat 95) (codeMat 226) (codeMat 141) false
    det95 det226 inv226
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3225_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 209, 38, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3225_orbit
  simpa only [lower278] using h

theorem space3226_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [258, 240, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(258, 338), (240, 97), (10, 306), (7, 2)]
    (codeMat 142) (codeMat 346) (codeMat 459) true
    det142 det346 inv346
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3226_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 240, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space3226_orbit
  simpa only [lower278] using h

theorem space3227_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 32), (8, 320), (5, 1), (2, 2)]
    (codeMat 161) (codeMat 337) (codeMat 337) false
    det161 det337 inv337
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3227_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3227_orbit
  simpa only [lower270] using h

theorem space3228_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [258, 34, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(258, 34), (34, 33), (10, 353), (6, 32)]
    (codeMat 107) (codeMat 87) (codeMat 468) true
    det107 det87 inv87
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3228_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 34, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 270 space3228_orbit
  simpa only [lower270] using h

theorem space3229_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 36, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 2), (36, 1), (8, 320), (2, 32)]
    (codeMat 99) (codeMat 84) (codeMat 84) true
    det99 det84 inv84
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3229_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 36, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3229_orbit
  simpa only [lower270] using h

theorem space3230_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [258, 34, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(258, 353), (34, 321), (18, 320), (10, 323)]
    (codeMat 242) (codeMat 458) (codeMat 458) false
    det242 det458 inv458
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3230_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 34, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 270 space3230_orbit
  simpa only [lower270] using h

theorem space3231_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 48, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 32), (48, 1), (8, 2), (2, 320)]
    (codeMat 98) (codeMat 394) (codeMat 330) false
    det98 det394 inv394
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3231_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 48, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3231_orbit
  simpa only [lower270] using h


end QiushiMatmul.FrozenWang
