import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4128_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 129, 80, 33, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (129, 139), (80, 252), (33, 148), (4, 2), (3, 130)]
    (codeMat 141) (codeMat 94) (codeMat 500) true
    det141 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4128_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 80, 33, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4128_orbit
  simpa only [lower35] using h

theorem space4129_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [264, 137, 81, 41, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(264, 224), (137, 151), (81, 148), (41, 104), (5, 8), (3, 1)]
    (codeMat 185) (codeMat 474) (codeMat 395) true
    det185 det474 inv474
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4129_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 137, 81, 41, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4129_orbit
  simpa only [lower35] using h

theorem space4130_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [256, 128, 80, 33, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(256, 2), (128, 1), (80, 68), (33, 160), (4, 16), (2, 8)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    det140 det98 inv98
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space4130_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 80, 33, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 29 space4130_orbit
  simpa only [lower29] using h

theorem space4131_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 129, 80, 32, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 20), (129, 28), (80, 224), (32, 128), (4, 2), (2, 3)]
    (codeMat 161) (codeMat 114) (codeMat 204) false
    det161 det114 inv114
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4131_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 80, 32, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4131_orbit
  simpa only [lower35] using h

theorem space4132_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [276, 144, 84, 50, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(276, 316), (144, 438), (84, 317), (50, 170), (1, 128)]
    (codeMat 460) (codeMat 470) (codeMat 213) true
    det460 det470 inv470
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4132_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 144, 84, 50, 1]) := by
  have h := frozenWangTable.lower_le_L0 189 space4132_orbit
  simpa only [lower189] using h

theorem space4133_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 80, 34, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (128, 8), (80, 96), (34, 20), (4, 2), (1, 128)]
    (codeMat 140) (codeMat 84) (codeMat 84) true
    det140 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4133_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 80, 34, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4133_orbit
  simpa only [lower35] using h

theorem space4134_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [273, 146, 84, 49, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(273, 267), (146, 325), (84, 266), (49, 272), (9, 16)]
    (codeMat 157) (codeMat 174) (codeMat 359) false
    det157 det174 inv174
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4134_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 146, 84, 49, 9]) := by
  have h := frozenWangTable.lower_le_L0 149 space4134_orbit
  simpa only [lower149] using h

theorem space4135_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [276, 147, 84, 48, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(276, 439), (147, 413), (84, 311), (48, 1), (15, 33)]
    (codeMat 226) (codeMat 445) (codeMat 478) true
    det226 det445 inv445
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4135_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 147, 84, 48, 15]) := by
  have h := frozenWangTable.lower_le_L0 189 space4135_orbit
  simpa only [lower189] using h

theorem space4136_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [276, 145, 84, 49, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(276, 287), (145, 347), (84, 286), (49, 160), (13, 496), (3, 320)]
    (codeMat 92) (codeMat 382) (codeMat 499) false
    det92 det382 inv382
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4136_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 145, 84, 49, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4136_orbit
  simpa only [lower65] using h

theorem space4137_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [274, 150, 84, 52, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(274, 191), (150, 283), (84, 431), (52, 356), (12, 357), (1, 260)]
    (codeMat 98) (codeMat 375) (codeMat 491) true
    det98 det375 inv375
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4137_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 150, 84, 52, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 80 space4137_orbit
  simpa only [lower80] using h

theorem space4138_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [275, 146, 80, 49, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(275, 122), (146, 27), (80, 437), (49, 96), (10, 368), (4, 16)]
    (codeMat 206) (codeMat 115) (codeMat 492) false
    det206 det115 inv115
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4138_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 80, 49, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space4138_orbit
  simpa only [lower69] using h

theorem space4139_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [272, 145, 80, 50, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(272, 223), (145, 191), (80, 367), (50, 452), (10, 453), (4, 192)]
    (codeMat 106) (codeMat 247) (codeMat 379) false
    det106 det247 inv247
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4139_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 145, 80, 50, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 80 space4139_orbit
  simpa only [lower80] using h

theorem space4140_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 131, 81, 32, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 136), (131, 224), (81, 28), (32, 1), (8, 3), (5, 128)]
    (codeMat 106) (codeMat 141) (codeMat 226) false
    det106 det141 inv141
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4140_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 81, 32, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space4140_orbit
  simpa only [lower35] using h

theorem space4141_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [274, 144, 82, 51, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(274, 223), (144, 27), (82, 222), (51, 352), (11, 368), (6, 256)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    det84 det382 inv382
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4141_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 144, 82, 51, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space4141_orbit
  simpa only [lower69] using h

theorem space4142_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 145, 82, 50, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 420), (145, 446), (82, 447), (50, 160), (11, 496), (6, 16)]
    (codeMat 205) (codeMat 473) (codeMat 409) false
    det205 det473 inv473
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4142_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 145, 82, 50, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space4142_orbit
  simpa only [lower65] using h

theorem space4143_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [272, 145, 82, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(272, 97), (145, 197), (82, 222), (50, 352), (10, 368), (6, 256)]
    (codeMat 87) (codeMat 206) (codeMat 498) false
    det87 det206 inv206
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4143_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 145, 82, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space4143_orbit
  simpa only [lower69] using h

theorem space4144_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 145, 82, 50, 8, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 436), (145, 430), (82, 437), (50, 176), (8, 320), (6, 16)]
    (codeMat 140) (codeMat 465) (codeMat 465) false
    det140 det465 inv465
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4144_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 145, 82, 50, 8, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space4144_orbit
  simpa only [lower65] using h

theorem space4145_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [275, 146, 80, 49, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(275, 122), (146, 27), (80, 452), (49, 96), (8, 256), (4, 16)]
    (codeMat 142) (codeMat 114) (codeMat 204) false
    det142 det114 inv114
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4145_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 146, 80, 49, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space4145_orbit
  simpa only [lower69] using h

theorem space4146_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 146, 81, 49, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 287), (146, 27), (81, 26), (49, 160), (8, 16), (5, 320)]
    (codeMat 85) (codeMat 318) (codeMat 299) false
    det85 det318 inv318
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4146_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 146, 81, 49, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space4146_orbit
  simpa only [lower65] using h

theorem space4147_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [275, 145, 83, 50, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(275, 443), (145, 31), (83, 11), (50, 356), (9, 1), (7, 260)]
    (codeMat 107) (codeMat 311) (codeMat 307) true
    det107 det311 inv311
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4147_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 145, 83, 50, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 80 space4147_orbit
  simpa only [lower80] using h

theorem space4148_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [278, 148, 84, 54, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(278, 287), (148, 255), (84, 239), (54, 260), (14, 261), (1, 320)]
    (codeMat 98) (codeMat 247) (codeMat 379) false
    det98 det247 inv247
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4148_lower : 15 ≤ frozenWangTable.L0 (spanCodes [278, 148, 84, 54, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4148_orbit
  simpa only [lower65] using h

theorem space4149_orbit :
    frozenWangTable.OrbitImage 190 (spanCodes [259, 135, 67, 36, 23]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 190 [(259, 11), (135, 33), (67, 43), (36, 128), (23, 356)]
    (codeMat 229) (codeMat 234) (codeMat 461) false
    det229 det234 inv234
    (by rw [basis190]; decide +kernel)
    (by rw [basis190]; decide +kernel)

theorem space4149_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 67, 36, 23]) := by
  have h := frozenWangTable.lower_le_L0 190 space4149_orbit
  simpa only [lower190] using h

theorem space4150_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [256, 142, 73, 45, 29]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(256, 27), (142, 351), (73, 1), (45, 16), (29, 272)]
    (codeMat 159) (codeMat 183) (codeMat 419) false
    det159 det183 inv183
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4150_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 142, 73, 45, 29]) := by
  have h := frozenWangTable.lower_le_L0 149 space4150_orbit
  simpa only [lower149] using h

theorem space4151_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [261, 135, 68, 36, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(261, 427), (135, 378), (68, 350), (36, 192), (16, 16)]
    (codeMat 215) (codeMat 124) (codeMat 124) false
    det215 det124 inv124
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4151_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 68, 36, 16]) := by
  have h := frozenWangTable.lower_le_L0 220 space4151_orbit
  simpa only [lower220] using h

theorem space4152_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 142, 74, 44, 30, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 447), (142, 161), (74, 69), (44, 336), (30, 160), (1, 320)]
    (codeMat 94) (codeMat 359) (codeMat 174) false
    det94 det359 inv359
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4152_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 142, 74, 44, 30, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4152_orbit
  simpa only [lower65] using h

theorem space4153_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [265, 133, 73, 36, 29, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(265, 26), (133, 69), (73, 27), (36, 16), (29, 496), (2, 320)]
    (codeMat 92) (codeMat 171) (codeMat 485) false
    det92 det171 inv171
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4153_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 133, 73, 36, 29, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space4153_orbit
  simpa only [lower65] using h

theorem space4154_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 136, 77, 40, 25, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 191), (136, 97), (77, 453), (40, 16), (25, 352), (3, 256)]
    (codeMat 87) (codeMat 359) (codeMat 174) false
    det87 det359 inv359
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4154_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 136, 77, 40, 25, 3]) := by
  have h := frozenWangTable.lower_le_L0 69 space4154_orbit
  simpa only [lower69] using h

theorem space4155_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 137, 72, 41, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 197), (137, 479), (72, 27), (41, 368), (28, 96), (3, 256)]
    (codeMat 93) (codeMat 415) (codeMat 253) false
    det93 det415 inv415
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4155_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 137, 72, 41, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 69 space4155_orbit
  simpa only [lower69] using h

theorem space4156_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 128, 64, 33, 20, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 8), (128, 2), (64, 128), (33, 224), (20, 28), (2, 3)]
    (codeMat 165) (codeMat 98) (codeMat 140) true
    det165 det98 inv98
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4156_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 64, 33, 20, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4156_orbit
  simpa only [lower35] using h

theorem space4157_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [270, 132, 78, 38, 26, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(270, 286), (132, 447), (78, 261), (38, 496), (26, 336), (1, 320)]
    (codeMat 95) (codeMat 499) (codeMat 382) false
    det95 det499 inv499
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4157_lower : 15 ≤ frozenWangTable.L0 (spanCodes [270, 132, 78, 38, 26, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4157_orbit
  simpa only [lower65] using h

theorem space4158_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [257, 137, 75, 42, 27, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(257, 357), (137, 368), (75, 272), (42, 223), (27, 192), (4, 260)]
    (codeMat 117) (codeMat 412) (codeMat 111) true
    det117 det412 inv412
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4158_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 137, 75, 42, 27, 4]) := by
  have h := frozenWangTable.lower_le_L0 80 space4158_orbit
  simpa only [lower80] using h

theorem space4159_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 67, 35, 17, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (128, 9), (67, 139), (35, 227), (17, 252), (6, 3)]
    (codeMat 172) (codeMat 122) (codeMat 460) true
    det172 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4159_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 35, 17, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space4159_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
