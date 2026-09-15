import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2912_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [130, 96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(130, 3), (96, 297), (18, 2), (10, 34)]
    (codeMat 158) (codeMat 271) (codeMat 314) true
    det158 det271 inv271
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2912_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space2912_orbit
  simpa only [lower269] using h

theorem space2913_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [128, 96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(128, 1), (96, 265), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    det156 det267 inv267
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2913_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space2913_orbit
  simpa only [lower269] using h

theorem space2914_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [146, 82, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(146, 128), (82, 129), (50, 170), (10, 138)]
    (codeMat 468) (codeMat 285) (codeMat 317) false
    det468 det285 inv285
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2914_lower : 16 ≤ frozenWangTable.L0 (spanCodes [146, 82, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 292 space2914_orbit
  simpa only [lower292] using h

theorem space2915_orbit :
    frozenWangTable.OrbitImage 274 (spanCodes [146, 67, 35, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 274 [(146, 1), (67, 82), (35, 240), (10, 80)]
    (codeMat 87) (codeMat 298) (codeMat 270) false
    det87 det298 inv298
    (by rw [basis274]; decide +kernel)
    (by rw [basis274]; decide +kernel)

theorem space2915_lower : 16 ≤ frozenWangTable.L0 (spanCodes [146, 67, 35, 10]) := by
  have h := frozenWangTable.lower_le_L0 274 space2915_orbit
  simpa only [lower274] using h

theorem space2916_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [163, 96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(163, 117), (96, 119), (18, 32), (10, 33)]
    (codeMat 234) (codeMat 313) (codeMat 313) true
    det234 det313 inv313
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2916_lower : 16 ≤ frozenWangTable.L0 (spanCodes [163, 96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space2916_orbit
  simpa only [lower267] using h

theorem space2917_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [130, 80, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(130, 128), (80, 11), (48, 32), (10, 138)]
    (codeMat 342) (codeMat 313) (codeMat 313) false
    det342 det313 inv313
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2917_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 80, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 292 space2917_orbit
  simpa only [lower292] using h

theorem space2918_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [288, 96, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(288, 2), (96, 34), (10, 118), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    det305 det141 inv141
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2918_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 96, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 267 space2918_orbit
  simpa only [lower267] using h

theorem space2919_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [288, 96, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(288, 32), (96, 34), (10, 118), (5, 1)]
    (codeMat 417) (codeMat 169) (codeMat 225) true
    det417 det169 inv169
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2919_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 96, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 267 space2919_orbit
  simpa only [lower267] using h

theorem space2920_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [260, 130, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(260, 1), (130, 2), (96, 96), (10, 274)]
    (codeMat 165) (codeMat 84) (codeMat 84) false
    det165 det84 inv84
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2920_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 130, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space2920_orbit
  simpa only [lower276] using h

theorem space2921_orbit :
    frozenWangTable.OrbitImage 275 (spanCodes [293, 163, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 275 [(293, 160), (163, 161), (96, 162), (10, 246)]
    (codeMat 117) (codeMat 458) (codeMat 458) false
    det117 det458 inv458
    (by rw [basis275]; decide +kernel)
    (by rw [basis275]; decide +kernel)

theorem space2921_lower : 16 ≤ frozenWangTable.L0 (spanCodes [293, 163, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 275 space2921_orbit
  simpa only [lower275] using h

theorem space2922_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [384, 96, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(384, 1), (96, 96), (10, 274), (6, 2)]
    (codeMat 140) (codeMat 114) (codeMat 204) true
    det140 det114 inv114
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2922_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 96, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 276 space2922_orbit
  simpa only [lower276] using h

theorem space2923_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [263, 146, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(263, 97), (146, 2), (96, 368), (10, 274)]
    (codeMat 167) (codeMat 348) (codeMat 125) false
    det167 det348 inv348
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2923_lower : 16 ≤ frozenWangTable.L0 (spanCodes [263, 146, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space2923_orbit
  simpa only [lower276] using h

theorem space2924_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [402, 96, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(402, 371), (96, 96), (10, 274), (7, 2)]
    (codeMat 142) (codeMat 370) (codeMat 207) true
    det142 det370 inv370
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2924_lower : 16 ≤ frozenWangTable.L0 (spanCodes [402, 96, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 276 space2924_orbit
  simpa only [lower276] using h

theorem space2925_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [291, 178, 96, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(291, 17), (178, 79), (96, 332), (10, 280), (7, 16)]
    (codeMat 207) (codeMat 214) (codeMat 214) false
    det207 det214 inv214
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2925_lower : 16 ≤ frozenWangTable.L0 (spanCodes [291, 178, 96, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 150 space2925_orbit
  simpa only [lower150] using h

theorem space2926_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [288, 128, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(288, 32), (128, 1), (96, 34), (10, 118)]
    (codeMat 116) (codeMat 330) (codeMat 394) false
    det116 det330 inv330
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2926_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 128, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space2926_orbit
  simpa only [lower267] using h

theorem space2927_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [275, 132, 86, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(275, 213), (132, 191), (86, 206), (54, 16), (10, 112)]
    (codeMat 94) (codeMat 478) (codeMat 445) false
    det94 det478 inv478
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2927_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 132, 86, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2927_orbit
  simpa only [lower152] using h

theorem space2928_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [263, 147, 80, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(263, 78), (147, 332), (80, 333), (48, 16), (10, 264)]
    (codeMat 213) (codeMat 481) (codeMat 185) false
    det213 det481 inv481
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2928_lower : 16 ≤ frozenWangTable.L0 (spanCodes [263, 147, 80, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2928_orbit
  simpa only [lower150] using h

theorem space2929_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 163, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 1), (163, 99), (96, 97), (10, 338)]
    (codeMat 229) (codeMat 215) (codeMat 342) false
    det229 det215 inv215
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2929_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 163, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2929_orbit
  simpa only [lower278] using h

theorem space2930_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [293, 130, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(293, 306), (130, 1), (96, 304), (10, 97)]
    (codeMat 277) (codeMat 354) (codeMat 142) false
    det277 det354 inv354
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2930_lower : 16 ≤ frozenWangTable.L0 (spanCodes [293, 130, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2930_orbit
  simpa only [lower278] using h

theorem space2931_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [390, 65, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(390, 1), (65, 2), (33, 304), (10, 336)]
    (codeMat 93) (codeMat 442) (codeMat 334) false
    det93 det442 inv442
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2931_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 65, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2931_orbit
  simpa only [lower278] using h

theorem space2932_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [402, 85, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(402, 338), (85, 337), (53, 304), (10, 306)]
    (codeMat 158) (codeMat 375) (codeMat 491) true
    det158 det375 inv375
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2932_lower : 16 ≤ frozenWangTable.L0 (spanCodes [402, 85, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2932_orbit
  simpa only [lower278] using h

theorem space2933_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [416, 96, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(416, 306), (96, 304), (10, 97), (7, 1)]
    (codeMat 161) (codeMat 426) (codeMat 335) true
    det161 det426 inv426
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2933_lower : 16 ≤ frozenWangTable.L0 (spanCodes [416, 96, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space2933_orbit
  simpa only [lower278] using h

theorem space2934_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [288, 144, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(288, 2), (144, 1), (96, 34), (10, 118)]
    (codeMat 102) (codeMat 106) (codeMat 396) false
    det102 det106 inv106
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2934_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 144, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space2934_orbit
  simpa only [lower267] using h

theorem space2935_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [275, 132, 71, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(275, 174), (132, 197), (71, 196), (39, 112), (10, 96)]
    (codeMat 93) (codeMat 482) (codeMat 143) false
    det93 det482 inv482
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2935_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 132, 71, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2935_orbit
  simpa only [lower152] using h

theorem space2936_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [273, 149, 85, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(273, 123), (149, 191), (85, 190), (53, 96), (10, 112)]
    (codeMat 92) (codeMat 254) (codeMat 443) false
    det92 det254 inv254
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2936_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 149, 85, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2936_orbit
  simpa only [lower152] using h

theorem space2937_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [263, 177, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(263, 306), (177, 305), (96, 97), (10, 338)]
    (codeMat 247) (codeMat 467) (codeMat 339) false
    det247 det467 inv467
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2937_lower : 16 ≤ frozenWangTable.L0 (spanCodes [263, 177, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2937_orbit
  simpa only [lower278] using h

theorem space2938_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [292, 146, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(292, 2), (146, 1), (96, 336), (10, 97)]
    (codeMat 279) (codeMat 99) (codeMat 172) false
    det279 det99 inv99
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2938_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 146, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2938_orbit
  simpa only [lower278] using h

theorem space2939_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [384, 86, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(384, 1), (86, 99), (54, 2), (10, 306)]
    (codeMat 156) (codeMat 115) (codeMat 492) true
    det156 det115 inv115
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2939_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 86, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2939_orbit
  simpa only [lower278] using h

theorem space2940_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [432, 96, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(432, 2), (96, 304), (10, 97), (6, 1)]
    (codeMat 177) (codeMat 394) (codeMat 330) true
    det177 det394 inv394
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2940_lower : 16 ≤ frozenWangTable.L0 (spanCodes [432, 96, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 278 space2940_orbit
  simpa only [lower278] using h

theorem space2941_orbit :
    frozenWangTable.OrbitImage 93 (spanCodes [96, 16, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 93 [(96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis93]; decide +kernel)
    (by rw [basis93]; decide +kernel)

theorem space2941_lower : 15 ≤ frozenWangTable.L0 (spanCodes [96, 16, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 93 space2941_orbit
  simpa only [lower93] using h

theorem space2942_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [96, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(96, 164), (17, 11), (9, 2), (4, 32), (3, 8)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    det267 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2942_lower : 15 ≤ frozenWangTable.L0 (spanCodes [96, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2942_orbit
  simpa only [lower103] using h

theorem space2943_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [96, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(96, 166), (17, 11), (9, 2), (5, 32), (3, 8)]
    (codeMat 331) (codeMat 314) (codeMat 271) false
    det331 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2943_lower : 15 ≤ frozenWangTable.L0 (spanCodes [96, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2943_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
