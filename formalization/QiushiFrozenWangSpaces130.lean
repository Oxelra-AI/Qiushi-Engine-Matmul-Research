import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4160_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [264, 131, 72, 32, 26, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(264, 26), (131, 447), (72, 1), (32, 16), (26, 496), (6, 320)]
    (codeMat 86) (codeMat 179) (codeMat 421) false
    det86 det179 inv179
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4160_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 131, 72, 32, 26, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space4160_orbit
  simpa only [lower65] using h

theorem space4161_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [266, 137, 64, 42, 19, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(266, 181), (137, 283), (64, 192), (42, 180), (19, 420), (7, 432)]
    (codeMat 214) (codeMat 86) (codeMat 212) true
    det214 det86 inv86
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4161_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 137, 64, 42, 19, 7]) := by
  have h := frozenWangTable.lower_le_L0 80 space4161_orbit
  simpa only [lower80] using h

theorem space4162_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [266, 128, 73, 35, 26, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(266, 107), (128, 1), (73, 260), (35, 368), (26, 96), (7, 432)]
    (codeMat 212) (codeMat 102) (codeMat 156) false
    det212 det102 inv102
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4162_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 128, 73, 35, 26, 7]) := by
  have h := frozenWangTable.lower_le_L0 80 space4162_orbit
  simpa only [lower80] using h

theorem space4163_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [265, 130, 72, 33, 27, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(265, 447), (130, 260), (72, 1), (33, 496), (27, 320), (7, 16)]
    (codeMat 206) (codeMat 421) (codeMat 179) false
    det206 det421 inv421
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4163_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 130, 72, 33, 27, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4163_orbit
  simpa only [lower65] using h

theorem space4164_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [266, 139, 67, 40, 18, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(266, 116), (139, 28), (67, 224), (40, 130), (18, 3), (5, 128)]
    (codeMat 107) (codeMat 370) (codeMat 207) false
    det107 det370 inv370
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4164_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 139, 67, 40, 18, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space4164_orbit
  simpa only [lower35] using h

theorem space4165_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 66, 35, 18, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (128, 2), (66, 22), (35, 104), (18, 128), (4, 8)]
    (codeMat 204) (codeMat 92) (codeMat 116) false
    det204 det92 inv92
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4165_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 35, 18, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space4165_orbit
  simpa only [lower35] using h

theorem space4166_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [266, 128, 72, 35, 24, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(266, 171), (128, 16), (72, 27), (35, 69), (24, 1), (4, 320)]
    (codeMat 98) (codeMat 285) (codeMat 317) false
    det98 det285 inv285
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4166_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 128, 72, 35, 24, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space4166_orbit
  simpa only [lower65] using h

theorem space4167_orbit :
    frozenWangTable.OrbitImage 80 (spanCodes [265, 136, 67, 43, 16, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 80 [(265, 170), (136, 283), (67, 223), (43, 96), (16, 192), (7, 432)]
    (codeMat 157) (codeMat 123) (codeMat 236) false
    det157 det123 inv123
    (by rw [basis80]; decide +kernel)
    (by rw [basis80]; decide +kernel)

theorem space4167_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 136, 67, 43, 16, 7]) := by
  have h := frozenWangTable.lower_le_L0 80 space4167_orbit
  simpa only [lower80] using h

theorem space4168_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [267, 130, 75, 33, 24, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(267, 431), (130, 27), (75, 430), (33, 496), (24, 320), (7, 16)]
    (codeMat 140) (codeMat 382) (codeMat 499) false
    det140 det382 inv382
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4168_lower : 15 ≤ frozenWangTable.L0 (spanCodes [267, 130, 75, 33, 24, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4168_orbit
  simpa only [lower65] using h

theorem space4169_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [265, 131, 72, 32, 27, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(265, 490), (131, 436), (72, 16), (32, 320), (27, 260), (7, 1)]
    (codeMat 177) (codeMat 412) (codeMat 111) false
    det177 det412 inv412
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4169_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 131, 72, 32, 27, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4169_orbit
  simpa only [lower65] using h

theorem space4170_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [265, 130, 73, 33, 26, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(265, 276), (130, 27), (73, 260), (33, 436), (26, 507), (7, 1)]
    (codeMat 417) (codeMat 370) (codeMat 207) false
    det417 det370 inv370
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4170_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 130, 73, 33, 26, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4170_orbit
  simpa only [lower65] using h

theorem space4171_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 66, 35, 16, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (128, 2), (66, 22), (35, 224), (16, 128), (6, 8)]
    (codeMat 140) (codeMat 124) (codeMat 124) false
    det140 det124 inv124
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4171_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 35, 16, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space4171_orbit
  simpa only [lower35] using h

theorem space4172_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 140, 74, 46, 30, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (140, 161), (74, 261), (46, 176), (30, 160), (1, 320)]
    (codeMat 87) (codeMat 103) (codeMat 188) false
    det87 det103 inv103
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4172_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 140, 74, 46, 30, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4172_orbit
  simpa only [lower65] using h

theorem space4173_orbit :
    frozenWangTable.OrbitImage 153 (spanCodes [256, 146, 83, 49, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 153 [(256, 16), (146, 27), (83, 363), (49, 257), (7, 256)]
    (codeMat 99) (codeMat 115) (codeMat 492) false
    det99 det115 inv115
    (by rw [basis153]; decide +kernel)
    (by rw [basis153]; decide +kernel)

theorem space4173_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 146, 83, 49, 7]) := by
  have h := frozenWangTable.lower_le_L0 153 space4173_orbit
  simpa only [lower153] using h

theorem space4174_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [291, 163, 65, 18, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(291, 283), (163, 282), (65, 325), (18, 16), (7, 256)]
    (codeMat 92) (codeMat 117) (codeMat 380) false
    det92 det117 inv117
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4174_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 163, 65, 18, 7]) := by
  have h := frozenWangTable.lower_le_L0 149 space4174_orbit
  simpa only [lower149] using h

theorem space4175_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [266, 128, 75, 35, 24, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(266, 94), (128, 320), (75, 430), (35, 17), (24, 27), (7, 16)]
    (codeMat 267) (codeMat 206) (codeMat 498) false
    det267 det206 inv206
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4175_lower : 15 ≤ frozenWangTable.L0 (spanCodes [266, 128, 75, 35, 24, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space4175_orbit
  simpa only [lower65] using h

theorem space4176_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 130, 67, 33, 19, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (130, 3), (67, 28), (33, 104), (19, 224), (4, 8)]
    (codeMat 205) (codeMat 86) (codeMat 212) false
    det205 det86 inv86
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4176_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 33, 19, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space4176_orbit
  simpa only [lower35] using h

theorem space4177_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 128, 69, 33, 17, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 3), (128, 9), (69, 28), (33, 224), (17, 96), (2, 8)]
    (codeMat 141) (codeMat 102) (codeMat 156) false
    det141 det102 inv102
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4177_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 69, 33, 17, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4177_orbit
  simpa only [lower35] using h

theorem space4178_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [289, 161, 65, 17, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(289, 127), (161, 124), (65, 128), (17, 96), (4, 9), (2, 8)]
    (codeMat 169) (codeMat 116) (codeMat 92) true
    det169 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4178_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 161, 65, 17, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4178_orbit
  simpa only [lower35] using h

theorem space4179_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [269, 132, 72, 36, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(269, 11), (132, 496), (72, 27), (36, 1), (28, 261), (3, 320)]
    (codeMat 107) (codeMat 157) (codeMat 486) false
    det107 det157 inv157
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4179_lower : 15 ≤ frozenWangTable.L0 (spanCodes [269, 132, 72, 36, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4179_orbit
  simpa only [lower65] using h

theorem space4180_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 141, 72, 45, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 260), (141, 187), (72, 1), (45, 320), (28, 176), (3, 16)]
    (codeMat 206) (codeMat 275) (codeMat 275) false
    det206 det275 inv275
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4180_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 141, 72, 45, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4180_orbit
  simpa only [lower65] using h

theorem space4181_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 141, 73, 45, 29, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 507), (141, 331), (73, 260), (45, 27), (29, 11), (3, 1)]
    (codeMat 401) (codeMat 486) (codeMat 157) false
    det401 det486 inv486
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4181_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 141, 73, 45, 29, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4181_orbit
  simpa only [lower65] using h

theorem space4182_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 146, 81, 49, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 37), (146, 192), (81, 228), (49, 398), (5, 16)]
    (codeMat 460) (codeMat 351) (codeMat 239) false
    det460 det351 inv351
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4182_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 146, 81, 49, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space4182_orbit
  simpa only [lower220] using h

theorem space4183_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 136, 74, 43, 27, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 368), (136, 447), (74, 463), (43, 26), (27, 1), (5, 16)]
    (codeMat 267) (codeMat 477) (codeMat 431) false
    det267 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space4183_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 136, 74, 43, 27, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space4183_orbit
  simpa only [lower69] using h

theorem space4184_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [267, 136, 67, 43, 19, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(267, 234), (136, 28), (67, 255), (43, 232), (19, 224), (4, 128)]
    (codeMat 86) (codeMat 233) (codeMat 233) false
    det86 det233 inv233
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4184_lower : 15 ≤ frozenWangTable.L0 (spanCodes [267, 136, 67, 43, 19, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space4184_orbit
  simpa only [lower35] using h

theorem space4185_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 141, 72, 45, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 430), (141, 177), (72, 27), (45, 320), (28, 160), (3, 16)]
    (codeMat 207) (codeMat 299) (codeMat 318) false
    det207 det299 inv299
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4185_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 141, 72, 45, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space4185_orbit
  simpa only [lower65] using h

theorem space4186_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 141, 72, 44, 28, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 447), (141, 421), (72, 1), (44, 496), (28, 480), (2, 320)]
    (codeMat 86) (codeMat 423) (codeMat 181) false
    det86 det423 inv423
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4186_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 141, 72, 44, 28, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space4186_orbit
  simpa only [lower65] using h

theorem space4187_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 128, 80, 33, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 20), (128, 2), (80, 148), (33, 104), (4, 8), (2, 1)]
    (codeMat 161) (codeMat 106) (codeMat 396) true
    det161 det106 inv106
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4187_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 128, 80, 33, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4187_orbit
  simpa only [lower35] using h

theorem space4188_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [262, 146, 84, 48, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(262, 138), (146, 1), (84, 171), (48, 128), (1, 438)]
    (codeMat 167) (codeMat 110) (codeMat 444) false
    det167 det110 inv110
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4188_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 146, 84, 48, 1]) := by
  have h := frozenWangTable.lower_le_L0 189 space4188_orbit
  simpa only [lower189] using h

theorem space4189_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [264, 136, 64, 42, 20, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(264, 150), (136, 149), (64, 2), (42, 96), (20, 232), (1, 128)]
    (codeMat 92) (codeMat 426) (codeMat 335) false
    det92 det426 inv426
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4189_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 136, 64, 42, 20, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4189_orbit
  simpa only [lower35] using h

theorem space4190_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 131, 65, 32, 21, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 22), (131, 148), (65, 2), (32, 9), (21, 104), (8, 1)]
    (codeMat 106) (codeMat 181) (codeMat 423) true
    det106 det181 inv181
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4190_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 65, 32, 21, 8]) := by
  have h := frozenWangTable.lower_le_L0 35 space4190_orbit
  simpa only [lower35] using h

theorem space4191_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 129, 64, 34, 20, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 232), (129, 104), (64, 8), (34, 150), (20, 148), (9, 1)]
    (codeMat 355) (codeMat 417) (codeMat 177) false
    det355 det417 inv417
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4191_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 64, 34, 20, 9]) := by
  have h := frozenWangTable.lower_le_L0 35 space4191_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
