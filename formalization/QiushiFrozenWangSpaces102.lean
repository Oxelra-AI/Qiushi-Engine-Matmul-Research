import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3264_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 65, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 269), (144, 32), (65, 390), (48, 1), (10, 294)]
    (codeMat 498) (codeMat 460) (codeMat 122) false
    det498 det460 inv460
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3264_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 65, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3264_orbit
  simpa only [lower187] using h

theorem space3265_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [258, 144, 66, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(258, 166), (144, 2), (66, 139), (48, 32), (10, 136)]
    (codeMat 214) (codeMat 313) (codeMat 313) false
    det214 det313 inv313
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3265_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 66, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 118 space3265_orbit
  simpa only [lower118] using h

theorem space3266_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 129, 65, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 43), (129, 33), (65, 32), (36, 390), (10, 269)]
    (codeMat 492) (codeMat 482) (codeMat 143) false
    det492 det482 inv482
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3266_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3266_orbit
  simpa only [lower187] using h

theorem space3267_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 80, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 294), (144, 32), (80, 33), (36, 390), (10, 269)]
    (codeMat 500) (codeMat 481) (codeMat 185) false
    det500 det481 inv481
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3267_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 80, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3267_orbit
  simpa only [lower187] using h

theorem space3268_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 145, 64, 52, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 118), (145, 131), (64, 9), (52, 232), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 307) (codeMat 311) false
    det95 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3268_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 145, 64, 52, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3268_orbit
  simpa only [lower35] using h

theorem space3269_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 208, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 97), (208, 252), (49, 129), (9, 130), (4, 8), (3, 9)]
    (codeMat 281) (codeMat 241) (codeMat 489) true
    det281 det241 inv241
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3269_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 208, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3269_orbit
  simpa only [lower35] using h

theorem space3270_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 83, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 294), (144, 128), (83, 129), (36, 390), (10, 139)]
    (codeMat 445) (codeMat 313) (codeMat 313) false
    det445 det313 inv313
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3270_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 83, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3270_orbit
  simpa only [lower187] using h

theorem space3271_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 65, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 139), (144, 128), (65, 390), (54, 1), (10, 294)]
    (codeMat 443) (codeMat 124) (codeMat 124) false
    det443 det124 inv124
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3271_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 65, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3271_orbit
  simpa only [lower187] using h

theorem space3272_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 146, 83, 32, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 137), (146, 3), (83, 252), (32, 8), (10, 224), (6, 128)]
    (codeMat 87) (codeMat 86) (codeMat 212) false
    det87 det86 inv86
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3272_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 83, 32, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3272_orbit
  simpa only [lower35] using h

theorem space3273_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 210, 48, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 429), (210, 295), (48, 390), (10, 263), (5, 128)]
    (codeMat 115) (codeMat 351) (codeMat 239) false
    det115 det351 inv351
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3273_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 210, 48, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 187 space3273_orbit
  simpa only [lower187] using h

theorem space3274_orbit :
    frozenWangTable.OrbitImage 157 (spanCodes [258, 146, 82, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 157 [(258, 148), (146, 128), (82, 129), (48, 32), (10, 138)]
    (codeMat 468) (codeMat 313) (codeMat 313) false
    det468 det313 inv313
    (by rw [basis157]; decide +kernel)
    (by rw [basis157]; decide +kernel)

theorem space3274_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 82, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 157 space3274_orbit
  simpa only [lower157] using h

theorem space3275_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 128, 66, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 134), (128, 2), (66, 133), (50, 164), (10, 173)]
    (codeMat 116) (codeMat 369) (codeMat 377) false
    det116 det369 inv369
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3275_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3275_orbit
  simpa only [lower103] using h

theorem space3276_orbit :
    frozenWangTable.OrbitImage 112 (spanCodes [258, 144, 85, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 112 [(258, 371), (144, 9), (85, 377), (53, 272), (10, 274)]
    (codeMat 158) (codeMat 351) (codeMat 239) true
    det158 det351 inv351
    (by rw [basis112]; decide +kernel)
    (by rw [basis112]; decide +kernel)

theorem space3276_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 85, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 112 space3276_orbit
  simpa only [lower112] using h

theorem space3277_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 194, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 164), (194, 173), (34, 132), (16, 2), (10, 135)]
    (codeMat 114) (codeMat 345) (codeMat 345) false
    det114 det345 inv345
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3277_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3277_orbit
  simpa only [lower103] using h

theorem space3278_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 135, 69, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 224), (135, 28), (69, 255), (34, 96), (16, 8), (10, 105)]
    (codeMat 114) (codeMat 345) (codeMat 345) true
    det114 det345 inv345
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3278_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 69, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3278_orbit
  simpa only [lower35] using h

theorem space3279_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 66, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (128, 8), (66, 97), (37, 252), (23, 28), (10, 227)]
    (codeMat 116) (codeMat 369) (codeMat 377) true
    det116 det369 inv369
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3279_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3279_orbit
  simpa only [lower35] using h

theorem space3280_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 130, 69, 38, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 139), (130, 9), (69, 252), (38, 136), (16, 8), (10, 104)]
    (codeMat 215) (codeMat 102) (codeMat 156) false
    det215 det102 inv102
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3280_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 69, 38, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3280_orbit
  simpa only [lower35] using h

theorem space3281_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 64, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 70), (128, 1), (64, 2), (34, 112), (16, 8), (10, 80)]
    (codeMat 84) (codeMat 298) (codeMat 270) false
    det84 det298 inv298
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3281_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 31 space3281_orbit
  simpa only [lower31] using h

theorem space3282_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 66, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 68), (128, 1), (66, 70), (32, 32), (16, 8), (10, 112)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    det84 det330 inv330
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3282_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 31 space3282_orbit
  simpa only [lower31] using h

theorem space3283_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 150, 65, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 139), (150, 10), (65, 390), (36, 128), (10, 429)]
    (codeMat 254) (codeMat 122) (codeMat 460) false
    det254 det122 inv122
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3283_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 150, 65, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3283_orbit
  simpa only [lower187] using h

theorem space3284_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 71, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 294), (144, 390), (71, 295), (36, 128), (10, 429)]
    (codeMat 253) (codeMat 185) (codeMat 481) false
    det253 det185 inv185
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3284_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 71, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3284_orbit
  simpa only [lower187] using h

theorem space3285_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 65, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 148), (132, 150), (65, 130), (39, 104), (17, 105), (10, 97)]
    (codeMat 107) (codeMat 499) (codeMat 382) true
    det107 det499 inv499
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3285_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 65, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3285_orbit
  simpa only [lower35] using h

theorem space3286_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 71, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 20), (132, 22), (71, 148), (38, 28), (22, 31), (10, 252)]
    (codeMat 111) (codeMat 122) (codeMat 460) true
    det111 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3286_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3286_orbit
  simpa only [lower35] using h

theorem space3287_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 150, 66, 38, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 227), (150, 28), (66, 97), (38, 224), (10, 104), (1, 8)]
    (codeMat 207) (codeMat 165) (codeMat 163) false
    det207 det165 inv165
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3287_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 150, 66, 38, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3287_orbit
  simpa only [lower35] using h

theorem space3288_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 67, 37, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 126), (128, 9), (67, 139), (37, 232), (18, 8), (10, 136)]
    (codeMat 159) (codeMat 299) (codeMat 318) false
    det159 det299 inv299
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3288_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 37, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3288_orbit
  simpa only [lower35] using h

theorem space3289_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 131, 65, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 20), (131, 30), (65, 3), (49, 136), (10, 232), (7, 8)]
    (codeMat 205) (codeMat 409) (codeMat 473) false
    det205 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3289_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3289_orbit
  simpa only [lower35] using h

theorem space3290_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 80, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 295), (144, 32), (80, 33), (53, 139), (10, 269)]
    (codeMat 500) (codeMat 485) (codeMat 171) false
    det500 det485 inv485
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3290_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 80, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3290_orbit
  simpa only [lower187] using h

theorem space3291_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 129, 65, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 42), (129, 33), (65, 32), (53, 139), (10, 269)]
    (codeMat 492) (codeMat 486) (codeMat 157) false
    det492 det486 inv486
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3291_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3291_orbit
  simpa only [lower187] using h

theorem space3292_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 65, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 22), (132, 20), (65, 128), (38, 31), (22, 28), (10, 224)]
    (codeMat 111) (codeMat 116) (codeMat 92) true
    det111 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3292_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 65, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3292_orbit
  simpa only [lower35] using h

theorem space3293_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 131, 67, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 224), (131, 28), (67, 31), (36, 128), (17, 20), (10, 22)]
    (codeMat 95) (codeMat 281) (codeMat 281) true
    det95 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3293_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3293_orbit
  simpa only [lower35] using h

theorem space3294_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 177, 65, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 42), (177, 171), (65, 32), (10, 295), (5, 1)]
    (codeMat 489) (codeMat 470) (codeMat 213) false
    det489 det470 inv470
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3294_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 177, 65, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 187 space3294_orbit
  simpa only [lower187] using h

theorem space3295_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 131, 65, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 22), (131, 28), (65, 3), (48, 128), (10, 224), (7, 8)]
    (codeMat 141) (codeMat 425) (codeMat 249) false
    det141 det425 inv425
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3295_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3295_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
