import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4192_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 131, 65, 32, 21, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 1), (131, 150), (65, 2), (32, 8), (21, 232), (9, 128)]
    (codeMat 213) (codeMat 156) (codeMat 102) false
    det213 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4192_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 65, 32, 21, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4192_orbit
  simpa only [lower35] using h

theorem space4193_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [257, 133, 65, 38, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(257, 180), (133, 272), (65, 260), (38, 191), (21, 464), (10, 453)]
    (codeMat 335) (codeMat 229) (codeMat 187) true
    det335 det229 inv229
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4193_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 38, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 80 space4193_orbit
  simpa only [lower80] using h

theorem space4194_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 135, 67, 36, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 436), (135, 437), (67, 223), (36, 16), (23, 430), (10, 479)]
    (codeMat 477) (codeMat 114) (codeMat 204) false
    det477 det114 inv114
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4194_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 67, 36, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space4194_orbit
  simpa only [lower69] using h

theorem space4195_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 71, 32, 19, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (131, 224), (71, 252), (32, 1), (19, 96), (11, 104)]
    (codeMat 114) (codeMat 204) (codeMat 114) true
    det114 det204 inv204
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4195_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 71, 32, 19, 11]) := by
  have h := frozenWangTable.lower_le_L0 35 space4195_orbit
  simpa only [lower35] using h

theorem space4196_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 135, 71, 36, 19, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 130), (135, 252), (71, 245), (36, 128), (19, 104), (11, 96)]
    (codeMat 214) (codeMat 225) (codeMat 169) false
    det214 det225 inv225
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4196_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 71, 36, 19, 11]) := by
  have h := frozenWangTable.lower_le_L0 35 space4196_orbit
  simpa only [lower35] using h

theorem space4197_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [258, 133, 68, 38, 16, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(258, 453), (133, 170), (68, 464), (38, 261), (16, 260), (12, 96)]
    (codeMat 163) (codeMat 458) (codeMat 458) true
    det163 det458 inv458
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4197_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 68, 38, 16, 12]) := by
  have h := frozenWangTable.lower_le_L0 80 space4197_orbit
  simpa only [lower80] using h

theorem space4198_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 64, 35, 20, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 20), (128, 128), (64, 130), (35, 28), (20, 224), (12, 227)]
    (codeMat 102) (codeMat 225) (codeMat 169) true
    det102 det225 inv225
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4198_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 35, 20, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4198_orbit
  simpa only [lower35] using h

theorem space4199_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 68, 39, 16, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (132, 96), (68, 105), (39, 20), (16, 128), (15, 150)]
    (codeMat 84) (codeMat 233) (codeMat 233) true
    det84 det233 inv233
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4199_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 39, 16, 15]) := by
  have h := frozenWangTable.lower_le_L0 35 space4199_orbit
  simpa only [lower35] using h

theorem space4200_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 129, 64, 34, 20, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 104), (129, 105), (64, 8), (34, 148), (20, 150), (15, 20)]
    (codeMat 92) (codeMat 442) (codeMat 334) true
    det92 det442 inv442
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4200_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 20, 15]) := by
  have h := frozenWangTable.lower_le_L0 35 space4200_orbit
  simpa only [lower35] using h

theorem space4201_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [256, 131, 67, 32, 23, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(256, 3), (131, 68), (67, 69), (32, 24), (23, 160), (15, 168)]
    (codeMat 84) (codeMat 229) (codeMat 187) false
    det84 det229 inv229
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4201_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 23, 15]) := by
  have h := frozenWangTable.lower_le_L0 29 space4201_orbit
  simpa only [lower29] using h

theorem space4202_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [262, 128, 72, 35, 28]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(262, 272), (128, 256), (72, 27), (35, 78), (28, 79)]
    (codeMat 299) (codeMat 425) (codeMat 249) false
    det299 det425 inv425
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4202_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 72, 35, 28]) := by
  have h := frozenWangTable.lower_le_L0 149 space4202_orbit
  simpa only [lower149] using h

theorem space4203_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 130, 65, 33, 21, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 22), (130, 128), (65, 2), (33, 31), (21, 224), (8, 3)]
    (codeMat 111) (codeMat 165) (codeMat 163) true
    det111 det165 inv165
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4203_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 130, 65, 33, 21, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4203_orbit
  simpa only [lower35] using h

theorem space4204_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [260, 131, 65, 32, 21, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(260, 3), (131, 68), (65, 1), (32, 24), (21, 160), (8, 8)]
    (codeMat 85) (codeMat 165) (codeMat 163) false
    det85 det165 inv165
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4204_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 65, 32, 21, 8]) := by
  have h := frozenWangTable.lower_le_L0 29 space4204_orbit
  simpa only [lower29] using h

theorem space4205_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 128, 66, 35, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 336), (128, 16), (66, 176), (35, 79), (22, 506), (10, 436)]
    (codeMat 355) (codeMat 372) (codeMat 93) false
    det355 det372 inv372
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4205_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 66, 35, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space4205_orbit
  simpa only [lower65] using h

theorem space4206_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 134, 68, 37, 16, 13]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 28), (134, 224), (68, 31), (37, 20), (16, 128), (13, 22)]
    (codeMat 87) (codeMat 169) (codeMat 225) true
    det87 det169 inv169
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4206_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 68, 37, 16, 13]) := by
  have h := frozenWangTable.lower_le_L0 35 space4206_orbit
  simpa only [lower35] using h

theorem space4207_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 65, 37, 21, 13]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 8), (134, 104), (65, 9), (37, 20), (21, 148), (13, 22)]
    (codeMat 85) (codeMat 185) (codeMat 481) true
    det85 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4207_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 65, 37, 21, 13]) := by
  have h := frozenWangTable.lower_le_L0 35 space4207_orbit
  simpa only [lower35] using h

theorem space4208_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 135, 69, 36, 17, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 130), (135, 126), (69, 139), (36, 128), (17, 232), (12, 136)]
    (codeMat 215) (codeMat 185) (codeMat 481) false
    det215 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4208_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 69, 36, 17, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4208_orbit
  simpa only [lower35] using h

theorem space4209_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [293, 163, 68, 16, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(293, 33), (163, 161), (68, 42), (16, 438), (12, 43)]
    (codeMat 494) (codeMat 183) (codeMat 419) true
    det494 det183 inv183
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4209_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 163, 68, 16, 12]) := by
  have h := frozenWangTable.lower_le_L0 189 space4209_orbit
  simpa only [lower189] using h

theorem space4210_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 70, 33, 18, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (130, 8), (70, 232), (33, 148), (18, 1), (12, 150)]
    (codeMat 299) (codeMat 330) (codeMat 394) false
    det299 det330 inv330
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4210_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 70, 33, 18, 12]) := by
  have h := frozenWangTable.lower_le_L0 35 space4210_orbit
  simpa only [lower35] using h

theorem space4211_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 130, 66, 33, 22, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 480), (130, 320), (66, 336), (33, 507), (22, 437), (15, 79)]
    (codeMat 354) (codeMat 239) (codeMat 351) false
    det354 det239 inv239
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4211_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 33, 22, 15]) := by
  have h := frozenWangTable.lower_le_L0 65 space4211_orbit
  simpa only [lower65] using h

theorem space4212_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 64, 37, 20, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (134, 96), (64, 9), (37, 252), (20, 224), (14, 31)]
    (codeMat 124) (codeMat 425) (codeMat 249) true
    det124 det425 inv425
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4212_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 37, 20, 14]) := by
  have h := frozenWangTable.lower_le_L0 35 space4212_orbit
  simpa only [lower35] using h

theorem space4213_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 138, 64, 40, 20, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 3), (138, 20), (64, 130), (40, 8), (20, 224), (1, 128)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    det85 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4213_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 138, 64, 40, 20, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4213_orbit
  simpa only [lower35] using h

theorem space4214_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [268, 128, 66, 34, 22, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(268, 164), (128, 1), (66, 10), (34, 446), (22, 113), (1, 16)]
    (codeMat 460) (codeMat 298) (codeMat 270) false
    det460 det298 inv298
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4214_lower : 15 ≤ frozenWangTable.L0 (spanCodes [268, 128, 66, 34, 22, 1]) := by
  have h := frozenWangTable.lower_le_L0 69 space4214_orbit
  simpa only [lower69] using h

theorem space4215_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 66, 37, 22, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 222), (134, 437), (66, 223), (37, 97), (22, 430), (11, 479)]
    (codeMat 468) (codeMat 342) (codeMat 215) false
    det468 det342 inv342
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4215_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 66, 37, 22, 11]) := by
  have h := frozenWangTable.lower_le_L0 69 space4215_orbit
  simpa only [lower69] using h

theorem space4216_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 128, 65, 35, 21, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 497), (128, 260), (65, 27), (35, 496), (21, 176), (11, 480)]
    (codeMat 215) (codeMat 141) (codeMat 226) false
    det215 det141 inv141
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4216_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 128, 65, 35, 21, 11]) := by
  have h := frozenWangTable.lower_le_L0 65 space4216_orbit
  simpa only [lower65] using h

theorem space4217_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 129, 71, 34, 19, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 507), (129, 436), (71, 506), (34, 480), (19, 176), (9, 16)]
    (codeMat 157) (codeMat 172) (codeMat 99) false
    det157 det172 inv172
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4217_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 71, 34, 19, 9]) := by
  have h := frozenWangTable.lower_le_L0 65 space4217_orbit
  simpa only [lower65] using h

theorem space4218_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 131, 70, 32, 18, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 506), (131, 437), (70, 507), (32, 16), (18, 320), (14, 480)]
    (codeMat 212) (codeMat 171) (codeMat 485) false
    det212 det171 inv171
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4218_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 131, 70, 32, 18, 14]) := by
  have h := frozenWangTable.lower_le_L0 65 space4218_orbit
  simpa only [lower65] using h

theorem space4219_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 131, 69, 32, 17, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 245), (131, 497), (69, 238), (32, 320), (17, 496), (14, 160)]
    (codeMat 159) (codeMat 334) (codeMat 442) false
    det159 det334 inv334
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4219_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 69, 32, 17, 14]) := by
  have h := frozenWangTable.lower_le_L0 65 space4219_orbit
  simpa only [lower65] using h

theorem space4220_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 133, 70, 38, 18, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 353), (133, 180), (70, 175), (38, 352), (18, 256), (12, 112)]
    (codeMat 215) (codeMat 205) (codeMat 242) false
    det215 det205 inv205
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4220_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 70, 38, 18, 12]) := by
  have h := frozenWangTable.lower_le_L0 69 space4220_orbit
  simpa only [lower69] using h

theorem space4221_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 70, 33, 18, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 150), (130, 1), (70, 149), (33, 232), (18, 8), (11, 96)]
    (codeMat 157) (codeMat 355) (codeMat 190) false
    det157 det355 inv355
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4221_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 70, 33, 18, 11]) := by
  have h := frozenWangTable.lower_le_L0 35 space4221_orbit
  simpa only [lower35] using h

theorem space4222_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 133, 70, 38, 18, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (133, 20), (70, 150), (38, 96), (18, 8), (11, 105)]
    (codeMat 107) (codeMat 345) (codeMat 345) true
    det107 det345 inv345
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4222_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 70, 38, 18, 11]) := by
  have h := frozenWangTable.lower_le_L0 35 space4222_orbit
  simpa only [lower35] using h

theorem space4223_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 135, 66, 36, 22, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 496), (135, 336), (66, 480), (36, 1), (22, 79), (11, 507)]
    (codeMat 355) (codeMat 159) (codeMat 230) false
    det355 det159 inv159
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4223_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 36, 22, 11]) := by
  have h := frozenWangTable.lower_le_L0 65 space4223_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
