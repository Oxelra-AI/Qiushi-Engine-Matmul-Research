import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3616_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 192, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 164), (192, 2), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    det161 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3616_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 192, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space3616_orbit
  simpa only [lower103] using h

theorem space3617_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 132, 68, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 224), (132, 28), (68, 20), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    det161 det282 inv282
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3617_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 132, 68, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3617_orbit
  simpa only [lower35] using h

theorem space3618_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 128, 64, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 118), (128, 9), (64, 1), (10, 22), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 275) (codeMat 275) true
    det140 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3618_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 128, 64, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3618_orbit
  simpa only [lower35] using h

theorem space3619_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 130, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 232), (130, 8), (64, 3), (10, 20), (6, 128), (1, 2)]
    (codeMat 141) (codeMat 305) (codeMat 305) true
    det141 det305 inv305
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3619_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 130, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3619_orbit
  simpa only [lower35] using h

theorem space3620_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 128, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 126), (128, 9), (64, 1), (10, 22), (6, 130), (1, 2)]
    (codeMat 140) (codeMat 307) (codeMat 311) true
    det140 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3620_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 128, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3620_orbit
  simpa only [lower35] using h

theorem space3621_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 130, 64, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 246), (130, 9), (64, 3), (10, 22), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 275) (codeMat 275) true
    det141 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3621_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 130, 64, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3621_orbit
  simpa only [lower35] using h

theorem space3622_orbit :
    frozenWangTable.OrbitImage 157 (spanCodes [256, 131, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 157 [(256, 128), (131, 52), (65, 32), (19, 53), (10, 30)]
    (codeMat 358) (codeMat 266) (codeMat 266) true
    det358 det266 inv266
    (by rw [basis157]; decide +kernel)
    (by rw [basis157]; decide +kernel)

theorem space3622_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 157 space3622_orbit
  simpa only [lower157] using h

theorem space3623_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 128, 67, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 175), (128, 2), (67, 42), (18, 3), (10, 35)]
    (codeMat 167) (codeMat 299) (codeMat 318) true
    det167 det299 inv299
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3623_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3623_orbit
  simpa only [lower103] using h

theorem space3624_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 130, 66, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 175), (130, 40), (66, 42), (18, 32), (10, 35)]
    (codeMat 230) (codeMat 313) (codeMat 313) true
    det230 det313 inv313
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3624_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3624_orbit
  simpa only [lower103] using h

theorem space3625_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [257, 128, 64, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(257, 118), (128, 1), (64, 9), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    det156 det267 inv267
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3625_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 101 space3625_orbit
  simpa only [lower101] using h

theorem space3626_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [273, 144, 64, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(273, 140), (144, 8), (64, 2), (8, 3), (2, 32)]
    (codeMat 102) (codeMat 305) (codeMat 305) true
    det102 det305 inv305
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3626_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 144, 64, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3626_orbit
  simpa only [lower103] using h

theorem space3627_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 192, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 164), (192, 2), (16, 8), (8, 9), (2, 32)]
    (codeMat 98) (codeMat 281) (codeMat 281) true
    det98 det281 inv281
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3627_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 192, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3627_orbit
  simpa only [lower103] using h

theorem space3628_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 145, 64, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 175), (145, 41), (64, 2), (9, 3), (3, 32)]
    (codeMat 103) (codeMat 307) (codeMat 311) true
    det103 det307 inv307
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3628_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 145, 64, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3628_orbit
  simpa only [lower103] using h

theorem space3629_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 165, 97, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (165, 239), (97, 245), (20, 480), (9, 320), (3, 16)]
    (codeMat 204) (codeMat 247) (codeMat 379) false
    det204 det247 inv247
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3629_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 165, 97, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space3629_orbit
  simpa only [lower65] using h

theorem space3630_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [275, 144, 65, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(275, 171), (144, 128), (65, 32), (10, 294), (7, 1)]
    (codeMat 425) (codeMat 372) (codeMat 93) false
    det425 det372 inv372
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3630_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 65, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 187 space3630_orbit
  simpa only [lower187] using h

theorem space3631_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 128, 64, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (128, 9), (64, 1), (22, 255), (10, 31), (1, 3)]
    (codeMat 172) (codeMat 275) (codeMat 275) true
    det172 det275 inv275
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3631_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 64, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3631_orbit
  simpa only [lower35] using h

theorem space3632_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 162, 114, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 149), (162, 150), (114, 117), (10, 105), (6, 1), (1, 8)]
    (codeMat 185) (codeMat 442) (codeMat 334) true
    det185 det442 inv442
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3632_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 162, 114, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3632_orbit
  simpa only [lower35] using h

theorem space3633_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [275, 128, 83, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(275, 461), (128, 1), (83, 463), (51, 493), (10, 118)]
    (codeMat 116) (codeMat 330) (codeMat 394) false
    det116 det330 inv330
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3633_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 128, 83, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3633_orbit
  simpa only [lower144] using h

theorem space3634_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 150, 66, 52, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 246), (150, 29), (66, 97), (52, 232), (10, 96), (1, 8)]
    (codeMat 206) (codeMat 419) (codeMat 183) false
    det206 det419 inv419
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3634_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 150, 66, 52, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3634_orbit
  simpa only [lower35] using h

theorem space3635_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [272, 133, 80, 52, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(272, 497), (133, 255), (80, 490), (52, 496), (9, 16), (3, 320)]
    (codeMat 95) (codeMat 158) (codeMat 358) false
    det95 det158 inv158
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3635_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 133, 80, 52, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space3635_orbit
  simpa only [lower65] using h

theorem space3636_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [275, 144, 65, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(275, 397), (144, 32), (65, 128), (50, 295), (10, 294)]
    (codeMat 370) (codeMat 428) (codeMat 107) false
    det370 det428 inv428
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3636_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 144, 65, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 187 space3636_orbit
  simpa only [lower187] using h

theorem space3637_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 147, 80, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 116), (147, 246), (80, 245), (33, 96), (10, 232), (6, 128)]
    (codeMat 93) (codeMat 465) (codeMat 465) false
    det93 det465 inv465
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3637_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 80, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3637_orbit
  simpa only [lower35] using h

theorem space3638_orbit :
    frozenWangTable.OrbitImage 72 (spanCodes [275, 145, 66, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 72 [(275, 311), (145, 11), (66, 81), (49, 296), (10, 80), (6, 32)]
    (codeMat 206) (codeMat 311) (codeMat 307) false
    det206 det311 inv311
    (by rw [basis72]; decide +kernel)
    (by rw [basis72]; decide +kernel)

theorem space3638_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 145, 66, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 72 space3638_orbit
  simpa only [lower72] using h

theorem space3639_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [275, 131, 80, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(275, 107), (131, 453), (80, 170), (49, 283), (10, 191), (6, 192)]
    (codeMat 117) (codeMat 491) (codeMat 375) false
    det117 det491 inv491
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space3639_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 131, 80, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 80 space3639_orbit
  simpa only [lower80] using h

theorem space3640_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 130, 81, 51, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 331), (130, 1), (81, 78), (51, 336), (10, 496), (5, 320)]
    (codeMat 93) (codeMat 110) (codeMat 444) false
    det93 det110 inv110
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3640_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 81, 51, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space3640_orbit
  simpa only [lower65] using h

theorem space3641_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 130, 80, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 337), (130, 260), (80, 255), (48, 320), (10, 480), (7, 16)]
    (codeMat 143) (codeMat 205) (codeMat 242) false
    det143 det205 inv205
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3641_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 80, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space3641_orbit
  simpa only [lower65] using h

theorem space3642_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 130, 83, 51, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 244), (130, 27), (83, 228), (51, 436), (10, 507), (7, 1)]
    (codeMat 417) (codeMat 351) (codeMat 239) false
    det417 det351 inv351
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3642_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 130, 83, 51, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space3642_orbit
  simpa only [lower65] using h

theorem space3643_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 162, 66, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 246), (162, 255), (66, 151), (10, 150), (4, 128), (1, 2)]
    (codeMat 142) (codeMat 403) (codeMat 403) true
    det142 det403 inv403
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3643_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 162, 66, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3643_orbit
  simpa only [lower35] using h

theorem space3644_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 162, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 127), (162, 119), (64, 128), (10, 151), (6, 1), (1, 2)]
    (codeMat 305) (codeMat 442) (codeMat 334) false
    det305 det442 inv442
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3644_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 162, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3644_orbit
  simpa only [lower35] using h

theorem space3645_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 145, 67, 51, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 99), (145, 139), (67, 245), (51, 227), (10, 252), (7, 3)]
    (codeMat 183) (codeMat 409) (codeMat 473) true
    det183 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3645_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 145, 67, 51, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3645_orbit
  simpa only [lower35] using h

theorem space3646_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [275, 147, 67, 49, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(275, 156), (147, 30), (67, 235), (49, 136), (10, 232), (7, 8)]
    (codeMat 207) (codeMat 409) (codeMat 473) false
    det207 det409 inv409
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3646_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 147, 67, 49, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space3646_orbit
  simpa only [lower35] using h

theorem space3647_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [275, 129, 83, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(275, 85), (129, 447), (83, 78), (48, 16), (10, 496), (4, 320)]
    (codeMat 86) (codeMat 478) (codeMat 445) false
    det86 det478 inv478
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3647_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 129, 83, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space3647_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
