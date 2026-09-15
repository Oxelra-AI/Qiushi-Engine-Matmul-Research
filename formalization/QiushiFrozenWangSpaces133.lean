import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4256_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 136, 80, 42, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 246), (136, 105), (80, 97), (42, 150), (4, 128), (1, 130)]
    (codeMat 142) (codeMat 467) (codeMat 339) true
    det142 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4256_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 136, 80, 42, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4256_orbit
  simpa only [lower35] using h

theorem space4257_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [271, 135, 65, 36, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(271, 279), (135, 43), (65, 438), (36, 128), (21, 42)]
    (codeMat 415) (codeMat 331) (codeMat 410) true
    det415 det331 inv331
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4257_lower : 15 ≤ frozenWangTable.L0 (spanCodes [271, 135, 65, 36, 21]) := by
  have h := frozenWangTable.lower_le_L0 189 space4257_orbit
  simpa only [lower189] using h

theorem space4258_orbit :
    frozenWangTable.OrbitImage 72 (spanCodes [259, 135, 67, 36, 23, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 72 [(259, 316), (135, 333), (67, 81), (36, 63), (23, 332), (14, 278)]
    (codeMat 494) (codeMat 302) (codeMat 302) false
    det494 det302 inv302
    (by rw [basis72]; decide +kernel)
    (by rw [basis72]; decide +kernel)

theorem space4258_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 67, 36, 23, 14]) := by
  have h := frozenWangTable.lower_le_L0 72 space4258_orbit
  simpa only [lower72] using h

theorem space4259_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 70, 33, 18, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (130, 1), (70, 97), (33, 252), (18, 3), (14, 227)]
    (codeMat 117) (codeMat 355) (codeMat 190) true
    det117 det355 inv355
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4259_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 33, 18, 14]) := by
  have h := frozenWangTable.lower_le_L0 35 space4259_orbit
  simpa only [lower35] using h

theorem space4260_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 71, 37, 19, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 126), (134, 119), (71, 139), (37, 232), (19, 224), (14, 136)]
    (codeMat 159) (codeMat 443) (codeMat 254) false
    det159 det443 inv443
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4260_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 71, 37, 19, 14]) := by
  have h := frozenWangTable.lower_le_L0 35 space4260_orbit
  simpa only [lower35] using h

theorem space4261_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 135, 70, 36, 18, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 224), (135, 227), (70, 31), (36, 128), (18, 130), (15, 22)]
    (codeMat 95) (codeMat 395) (codeMat 474) true
    det95 det395 inv395
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4261_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 70, 36, 18, 15]) := by
  have h := frozenWangTable.lower_le_L0 35 space4261_orbit
  simpa only [lower35] using h

theorem space4262_orbit :
    frozenWangTable.OrbitImage 72 (spanCodes [263, 134, 71, 37, 19, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 72 [(263, 90), (134, 278), (71, 101), (37, 376), (19, 344), (15, 264)]
    (codeMat 159) (codeMat 241) (codeMat 489) false
    det159 det241 inv241
    (by rw [basis72]; decide +kernel)
    (by rw [basis72]; decide +kernel)

theorem space4262_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 71, 37, 19, 15]) := by
  have h := frozenWangTable.lower_le_L0 72 space4262_orbit
  simpa only [lower72] using h

theorem space4263_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 130, 70, 33, 18, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 224), (130, 3), (70, 252), (33, 96), (18, 1), (12, 104)]
    (codeMat 115) (codeMat 330) (codeMat 394) true
    det115 det330 inv330
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4263_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 70, 33, 18, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4263_orbit
  simpa only [lower35] using h

theorem space4264_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 132, 68, 39, 16, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 363), (132, 436), (68, 437), (39, 463), (16, 16), (12, 430)]
    (codeMat 468) (codeMat 313) (codeMat 313) false
    det468 det313 inv313
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4264_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 132, 68, 39, 16, 12]) := by
  have h := frozenWangTable.lower_le_L0 69 space4264_orbit
  simpa only [lower69] using h

theorem space4265_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 69, 37, 17, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 222), (134, 437), (69, 436), (37, 272), (17, 96), (8, 256)]
    (codeMat 157) (codeMat 482) (codeMat 143) false
    det157 det482 inv482
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4265_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 69, 37, 17, 8]) := by
  have h := frozenWangTable.lower_le_L0 69 space4265_orbit
  simpa only [lower69] using h

theorem space4266_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [257, 129, 64, 34, 20, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(257, 68), (129, 70), (64, 1), (34, 160), (20, 176), (9, 8)]
    (codeMat 92) (codeMat 401) (codeMat 401) false
    det92 det401 inv401
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4266_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 20, 9]) := by
  have h := frozenWangTable.lower_le_L0 29 space4266_orbit
  simpa only [lower29] using h

theorem space4267_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 134, 71, 37, 19, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 224), (134, 255), (71, 28), (37, 96), (19, 105), (9, 8)]
    (codeMat 123) (codeMat 410) (codeMat 331) true
    det123 det410 inv410
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4267_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 71, 37, 19, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4267_orbit
  simpa only [lower35] using h

theorem space4268_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 147, 82, 48, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 224), (147, 246), (82, 30), (48, 130), (9, 3), (6, 128)]
    (codeMat 99) (codeMat 409) (codeMat 473) false
    det99 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4268_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 147, 82, 48, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space4268_orbit
  simpa only [lower35] using h

theorem space4269_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [282, 128, 83, 35, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(282, 351), (128, 16), (83, 378), (35, 228), (7, 192)]
    (codeMat 103) (codeMat 337) (codeMat 337) false
    det103 det337 inv337
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4269_lower : 15 ≤ frozenWangTable.L0 (spanCodes [282, 128, 83, 35, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space4269_orbit
  simpa only [lower220] using h

theorem space4270_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 128, 75, 35, 27, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 10), (128, 16), (75, 436), (35, 68), (27, 260), (4, 1)]
    (codeMat 161) (codeMat 92) (codeMat 116) false
    det161 det92 inv92
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4270_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 75, 35, 27, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space4270_orbit
  simpa only [lower65] using h

theorem space4271_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [264, 129, 64, 34, 16, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(264, 170), (129, 160), (64, 16), (34, 69), (16, 260), (4, 320)]
    (codeMat 99) (codeMat 396) (codeMat 106) false
    det99 det396 inv396
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4271_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 34, 16, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space4271_orbit
  simpa only [lower65] using h

theorem space4272_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 137, 65, 42, 17, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 26), (137, 197), (65, 27), (42, 96), (17, 368), (4, 16)]
    (codeMat 204) (codeMat 171) (codeMat 485) false
    det204 det171 inv171
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4272_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 137, 65, 42, 17, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space4272_orbit
  simpa only [lower69] using h

theorem space4273_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [264, 129, 64, 34, 17, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(264, 238), (129, 228), (64, 27), (34, 176), (17, 480), (5, 320)]
    (codeMat 95) (codeMat 425) (codeMat 249) false
    det95 det425 inv425
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4273_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 34, 17, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space4273_orbit
  simpa only [lower65] using h

theorem space4274_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 146, 81, 49, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 447), (146, 1), (81, 26), (49, 176), (8, 16), (5, 320)]
    (codeMat 87) (codeMat 302) (codeMat 302) false
    det87 det302 inv302
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4274_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 81, 49, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space4274_orbit
  simpa only [lower65] using h

theorem space4275_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 144, 84, 49, 12, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 246), (144, 2), (84, 125), (49, 96), (12, 232), (2, 128)]
    (codeMat 94) (codeMat 369) (codeMat 377) false
    det94 det369 inv369
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4275_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 144, 84, 49, 12, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4275_orbit
  simpa only [lower35] using h

theorem space4276_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 136, 81, 41, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 252), (136, 227), (81, 105), (41, 150), (5, 2), (2, 130)]
    (codeMat 143) (codeMat 491) (codeMat 375) true
    det143 det491 inv491
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4276_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 136, 81, 41, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4276_orbit
  simpa only [lower35] using h

theorem space4277_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 132, 72, 36, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 97), (132, 446), (72, 256), (36, 1), (28, 26), (3, 16)]
    (codeMat 395) (codeMat 212) (codeMat 86) false
    det395 det212 inv212
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4277_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 132, 72, 36, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 69 space4277_orbit
  simpa only [lower69] using h

theorem space4278_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [264, 129, 64, 33, 20, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(264, 78), (129, 68), (64, 1), (33, 496), (20, 160), (3, 320)]
    (codeMat 92) (codeMat 417) (codeMat 177) false
    det92 det417 inv417
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4278_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 33, 20, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4278_orbit
  simpa only [lower65] using h

theorem space4279_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 136, 81, 40, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 96), (136, 232), (81, 246), (40, 128), (5, 2), (3, 3)]
    (codeMat 177) (codeMat 458) (codeMat 458) false
    det177 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4279_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 136, 81, 40, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4279_orbit
  simpa only [lower35] using h

theorem space4280_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 137, 81, 41, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 254), (137, 118), (81, 126), (41, 150), (5, 2), (3, 1)]
    (codeMat 305) (codeMat 474) (codeMat 395) false
    det305 det474 inv474
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4280_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 137, 81, 41, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4280_orbit
  simpa only [lower35] using h

theorem space4281_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 131, 67, 32, 23, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 136), (131, 104), (67, 96), (32, 3), (23, 148), (15, 149)]
    (codeMat 354) (codeMat 229) (codeMat 187) false
    det354 det229 inv229
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4281_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 131, 67, 32, 23, 15]) := by
  have h := frozenWangTable.lower_le_L0 35 space4281_orbit
  simpa only [lower35] using h

theorem space4282_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 133, 65, 38, 21, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 507), (133, 436), (65, 1), (38, 480), (21, 176), (14, 496)]
    (codeMat 213) (codeMat 165) (codeMat 163) false
    det213 det165 inv165
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4282_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 65, 38, 21, 14]) := by
  have h := frozenWangTable.lower_le_L0 65 space4282_orbit
  simpa only [lower65] using h

theorem space4283_orbit :
    frozenWangTable.OrbitImage 72 (spanCodes [263, 132, 71, 39, 19, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 72 [(263, 265), (132, 91), (71, 310), (39, 264), (19, 344), (12, 112)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    det86 det94 inv94
    (by rw [basis72]; decide +kernel)
    (by rw [basis72]; decide +kernel)

theorem space4283_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 132, 71, 39, 19, 12]) := by
  have h := frozenWangTable.lower_le_L0 72 space4283_orbit
  simpa only [lower72] using h

theorem space4284_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 135, 66, 36, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 490), (135, 238), (66, 497), (36, 16), (22, 160), (10, 496)]
    (codeMat 158) (codeMat 177) (codeMat 417) false
    det158 det177 inv177
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4284_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 66, 36, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space4284_orbit
  simpa only [lower65] using h

theorem space4285_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 64, 35, 20, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (128, 128), (64, 2), (35, 252), (20, 224), (9, 3)]
    (codeMat 103) (codeMat 417) (codeMat 177) true
    det103 det417 inv417
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4285_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 35, 20, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4285_orbit
  simpa only [lower35] using h

theorem space4286_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 129, 64, 34, 20, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 128), (129, 148), (64, 2), (34, 96), (20, 104), (9, 1)]
    (codeMat 99) (codeMat 401) (codeMat 401) true
    det99 det401 inv401
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4286_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 34, 20, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4286_orbit
  simpa only [lower35] using h

theorem space4287_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 132, 67, 39, 23, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 31), (132, 252), (67, 224), (39, 22), (23, 148), (8, 128)]
    (codeMat 86) (codeMat 244) (codeMat 95) true
    det86 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4287_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 132, 67, 39, 23, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4287_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
