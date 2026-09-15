import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3232_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [257, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(257, 136), (36, 2), (20, 47), (9, 3), (3, 32)]
    (codeMat 331) (codeMat 187) (codeMat 229) false
    det331 det187 inv187
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3232_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 118 space3232_orbit
  simpa only [lower118] using h

theorem space3233_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 32, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 164), (32, 2), (18, 32), (10, 35), (7, 9)]
    (codeMat 282) (codeMat 233) (codeMat 233) false
    det282 det233 inv233
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3233_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 32, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space3233_orbit
  simpa only [lower103] using h

theorem space3234_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 133), (49, 33), (9, 40), (4, 2), (3, 3)]
    (codeMat 281) (codeMat 241) (codeMat 489) false
    det281 det241 inv241
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3234_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3234_orbit
  simpa only [lower103] using h

theorem space3235_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [257, 65, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(257, 321), (65, 1), (9, 2), (3, 32)]
    (codeMat 93) (codeMat 279) (codeMat 279) true
    det93 det279 inv279
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3235_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 65, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 270 space3235_orbit
  simpa only [lower270] using h

theorem space3236_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 65, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 320), (65, 1), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    det85 det273 inv273
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3236_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 65, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3236_orbit
  simpa only [lower270] using h

theorem space3237_orbit :
    frozenWangTable.OrbitImage 98 (spanCodes [258, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 98 [(258, 136), (64, 3), (10, 148), (6, 128), (1, 2)]
    (codeMat 141) (codeMat 177) (codeMat 417) true
    det141 det177 inv177
    (by rw [basis98]; decide +kernel)
    (by rw [basis98]; decide +kernel)

theorem space3237_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 98 space3237_orbit
  simpa only [lower98] using h

theorem space3238_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 67, 34, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 135), (67, 173), (34, 132), (10, 164), (4, 2)]
    (codeMat 143) (codeMat 141) (codeMat 226) true
    det143 det141 inv141
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3238_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 67, 34, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space3238_orbit
  simpa only [lower103] using h

theorem space3239_orbit :
    frozenWangTable.OrbitImage 157 (spanCodes [258, 65, 35, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 157 [(258, 138), (65, 1), (35, 160), (10, 148), (7, 128)]
    (codeMat 205) (codeMat 179) (codeMat 421) true
    det205 det179 inv179
    (by rw [basis157]; decide +kernel)
    (by rw [basis157]; decide +kernel)

theorem space3239_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 65, 35, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 157 space3239_orbit
  simpa only [lower157] using h

theorem space3240_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 66, 38, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 173), (66, 133), (38, 164), (10, 134), (1, 2)]
    (codeMat 207) (codeMat 165) (codeMat 163) true
    det207 det165 inv165
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3240_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 66, 38, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space3240_orbit
  simpa only [lower103] using h

theorem space3241_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [258, 65, 34, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(258, 166), (65, 32), (34, 139), (10, 136), (5, 2)]
    (codeMat 331) (codeMat 188) (codeMat 103) true
    det331 det188 inv188
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3241_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 65, 34, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 118 space3241_orbit
  simpa only [lower118] using h

theorem space3242_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 66, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 80), (66, 82), (32, 32), (10, 100), (4, 8), (1, 9)]
    (codeMat 161) (codeMat 169) (codeMat 225) true
    det161 det169 inv169
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3242_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 66, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space3242_orbit
  simpa only [lower31] using h

theorem space3243_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 144, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 320), (144, 1), (8, 32), (2, 2)]
    (codeMat 142) (codeMat 266) (codeMat 266) true
    det142 det266 inv266
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3243_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 144, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3243_orbit
  simpa only [lower270] using h

theorem space3244_orbit :
    frozenWangTable.OrbitImage 98 (spanCodes [258, 128, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 98 [(258, 28), (128, 3), (34, 20), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 106) (codeMat 396) true
    det86 det106 inv106
    (by rw [basis98]; decide +kernel)
    (by rw [basis98]; decide +kernel)

theorem space3244_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 98 space3244_orbit
  simpa only [lower98] using h

theorem space3245_orbit :
    frozenWangTable.OrbitImage 98 (spanCodes [258, 130, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 98 [(258, 136), (130, 128), (32, 3), (16, 2), (10, 148)]
    (codeMat 354) (codeMat 116) (codeMat 92) false
    det354 det116 inv116
    (by rw [basis98]; decide +kernel)
    (by rw [basis98]; decide +kernel)

theorem space3245_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 98 space3245_orbit
  simpa only [lower98] using h

theorem space3246_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [258, 130, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(258, 46), (130, 45), (36, 32), (20, 34), (10, 166)]
    (codeMat 214) (codeMat 122) (codeMat 460) true
    det214 det122 inv122
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3246_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 118 space3246_orbit
  simpa only [lower118] using h

theorem space3247_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 130, 38, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 43), (130, 3), (38, 34), (16, 2), (10, 134)]
    (codeMat 215) (codeMat 102) (codeMat 156) true
    det215 det102 inv102
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3247_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 38, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3247_orbit
  simpa only [lower103] using h

theorem space3248_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 144, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 294), (144, 390), (33, 33), (10, 43), (5, 1)]
    (codeMat 473) (codeMat 465) (codeMat 465) false
    det473 det465 inv465
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3248_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 187 space3248_orbit
  simpa only [lower187] using h

theorem space3249_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 146, 32, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 35), (146, 9), (32, 2), (10, 164), (6, 32)]
    (codeMat 87) (codeMat 86) (codeMat 212) true
    det87 det86 inv86
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3249_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 146, 32, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 103 space3249_orbit
  simpa only [lower103] using h

theorem space3250_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 32, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 22), (128, 2), (32, 9), (16, 1), (10, 68), (6, 32)]
    (codeMat 98) (codeMat 102) (codeMat 156) true
    det98 det102 inv102
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3250_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 32, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 31 space3250_orbit
  simpa only [lower31] using h

theorem space3251_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [258, 130, 66, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(258, 323), (130, 320), (66, 321), (10, 353)]
    (codeMat 372) (codeMat 482) (codeMat 143) false
    det372 det482 inv482
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3251_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 10]) := by
  have h := frozenWangTable.lower_le_L0 270 space3251_orbit
  simpa only [lower270] using h

theorem space3252_orbit :
    frozenWangTable.OrbitImage 270 (spanCodes [256, 192, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 270 [(256, 2), (192, 1), (8, 32), (2, 320)]
    (codeMat 84) (codeMat 226) (codeMat 141) false
    det84 det226 inv226
    (by rw [basis270]; decide +kernel)
    (by rw [basis270]; decide +kernel)

theorem space3252_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 192, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 270 space3252_orbit
  simpa only [lower270] using h

theorem space3253_orbit :
    frozenWangTable.OrbitImage 98 (spanCodes [258, 130, 64, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 98 [(258, 136), (130, 8), (64, 2), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 305) (codeMat 305) true
    det165 det305 inv305
    (by rw [basis98]; decide +kernel)
    (by rw [basis98]; decide +kernel)

theorem space3253_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 98 space3253_orbit
  simpa only [lower98] using h

theorem space3254_orbit :
    frozenWangTable.OrbitImage 187 (spanCodes [258, 178, 114, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 187 [(258, 263), (178, 295), (114, 161), (10, 429), (5, 128)]
    (codeMat 117) (codeMat 375) (codeMat 491) false
    det117 det375 inv375
    (by rw [basis187]; decide +kernel)
    (by rw [basis187]; decide +kernel)

theorem space3254_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 178, 114, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 187 space3254_orbit
  simpa only [lower187] using h

theorem space3255_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 130, 64, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 43), (130, 40), (64, 2), (10, 173), (7, 9)]
    (codeMat 172) (codeMat 426) (codeMat 335) false
    det172 det426 inv426
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3255_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space3255_orbit
  simpa only [lower103] using h

theorem space3256_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 194, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 35), (194, 42), (10, 135), (6, 3), (1, 2)]
    (codeMat 169) (codeMat 410) (codeMat 331) false
    det169 det410 inv410
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3256_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space3256_orbit
  simpa only [lower103] using h

theorem space3257_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 176, 114, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 137), (176, 255), (114, 117), (10, 105), (6, 9), (1, 8)]
    (codeMat 169) (codeMat 410) (codeMat 331) true
    det169 det410 inv410
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3257_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 176, 114, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3257_orbit
  simpa only [lower35] using h

theorem space3258_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [258, 129, 65, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(258, 35), (129, 47), (65, 2), (10, 168), (6, 32)]
    (codeMat 205) (codeMat 190) (codeMat 355) false
    det205 det190 inv190
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3258_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 118 space3258_orbit
  simpa only [lower118] using h

theorem space3259_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 64, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 22), (128, 2), (64, 1), (10, 80), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 305) (codeMat 305) false
    det140 det305 inv305
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3259_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space3259_orbit
  simpa only [lower31] using h

theorem space3260_orbit :
    frozenWangTable.OrbitImage 157 (spanCodes [258, 131, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 157 [(258, 148), (131, 52), (65, 32), (19, 53), (10, 30)]
    (codeMat 358) (codeMat 302) (codeMat 302) true
    det358 det302 inv302
    (by rw [basis157]; decide +kernel)
    (by rw [basis157]; decide +kernel)

theorem space3260_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 157 space3260_orbit
  simpa only [lower157] using h

theorem space3261_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [258, 128, 67, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(258, 135), (128, 2), (67, 42), (18, 3), (10, 35)]
    (codeMat 167) (codeMat 267) (codeMat 282) true
    det167 det267 inv267
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3261_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space3261_orbit
  simpa only [lower103] using h

theorem space3262_orbit :
    frozenWangTable.OrbitImage 118 (spanCodes [258, 129, 65, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 118 [(258, 168), (129, 47), (65, 45), (18, 32), (10, 35)]
    (codeMat 230) (codeMat 313) (codeMat 313) true
    det230 det313 inv313
    (by rw [basis118]; decide +kernel)
    (by rw [basis118]; decide +kernel)

theorem space3262_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 118 space3262_orbit
  simpa only [lower118] using h

theorem space3263_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 145, 64, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 132), (145, 41), (64, 2), (9, 3), (3, 32)]
    (codeMat 103) (codeMat 275) (codeMat 275) true
    det103 det275 inv275
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3263_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 145, 64, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3263_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
