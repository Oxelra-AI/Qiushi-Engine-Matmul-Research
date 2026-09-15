import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1056_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [291, 131, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(291, 14), (131, 274), (67, 164), (19, 306), (10, 166), (5, 45)]
    (codeMat 375) (codeMat 428) (codeMat 107) false
    det375 det428 inv428
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1056_lower : 14 ≤ frozenWangTable.L0 (spanCodes [291, 131, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1056_orbit
  simpa only [lower55] using h

theorem space1057_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [289, 131, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(289, 46), (131, 274), (65, 438), (19, 306), (10, 404), (5, 45)]
    (codeMat 311) (codeMat 236) (codeMat 123) false
    det311 det236 inv236
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1057_lower : 14 ≤ frozenWangTable.L0 (spanCodes [289, 131, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1057_orbit
  simpa only [lower55] using h

theorem space1058_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 197), (130, 1), (66, 391), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 93) (codeMat 335) (codeMat 426) false
    det93 det335 inv335
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1058_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1058_orbit
  simpa only [lower17] using h

theorem space1059_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 68), (128, 1), (65, 390), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    det84 det330 inv330
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1059_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1059_orbit
  simpa only [lower17] using h

theorem space1060_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 168), (128, 32), (66, 272), (38, 287), (19, 404), (10, 166)]
    (codeMat 359) (codeMat 492) (codeMat 115) false
    det359 det492 inv492
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1060_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1060_orbit
  simpa only [lower55] using h

theorem space1061_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 129, 66, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 136), (129, 304), (66, 272), (34, 139), (19, 306), (10, 166)]
    (codeMat 303) (codeMat 124) (codeMat 124) false
    det303 det124 inv124
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1061_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 129, 66, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1061_orbit
  simpa only [lower55] using h

theorem space1062_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 131, 67, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 3), (131, 164), (67, 274), (19, 166), (10, 306), (7, 45)]
    (codeMat 382) (codeMat 116) (codeMat 92) false
    det382 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1062_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 131, 67, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1062_orbit
  simpa only [lower55] using h

theorem space1063_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [291, 129, 66, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(291, 46), (129, 164), (66, 274), (19, 166), (10, 306), (7, 45)]
    (codeMat 311) (codeMat 116) (codeMat 92) false
    det311 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1063_lower : 14 ≤ frozenWangTable.L0 (spanCodes [291, 129, 66, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1063_orbit
  simpa only [lower55] using h

theorem space1064_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 195, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (195, 45), (35, 34), (19, 404), (10, 166), (7, 32)]
    (codeMat 92) (codeMat 213) (codeMat 470) true
    det92 det213 inv213
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1064_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 195, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1064_orbit
  simpa only [lower55] using h

theorem space1065_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 228), (131, 457), (65, 63), (35, 160), (19, 456), (10, 440), (7, 128)]
    (codeMat 94) (codeMat 331) (codeMat 410) false
    det94 det331 inv331
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1065_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1065_orbit
  simpa only [lower17] using h

theorem space1066_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 65, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 69), (128, 1), (65, 390), (35, 488), (19, 456), (10, 112), (7, 128)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    det84 det334 inv334
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1066_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1066_orbit
  simpa only [lower17] using h

theorem space1067_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 197), (130, 1), (64, 390), (35, 488), (19, 456), (10, 112), (7, 128)]
    (codeMat 85) (codeMat 334) (codeMat 442) false
    det85 det334 inv334
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1067_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1067_orbit
  simpa only [lower17] using h

theorem space1068_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 100), (129, 457), (64, 63), (35, 160), (19, 456), (10, 440), (7, 128)]
    (codeMat 95) (codeMat 331) (codeMat 410) false
    det95 det331 inv331
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1068_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1068_orbit
  simpa only [lower17] using h

theorem space1069_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [384, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(384, 3), (66, 287), (34, 132), (19, 166), (10, 306), (7, 32)]
    (codeMat 95) (codeMat 395) (codeMat 474) true
    det95 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1069_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1069_orbit
  simpa only [lower55] using h

theorem space1070_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 451), (129, 391), (65, 390), (34, 280), (19, 440), (10, 112), (7, 128)]
    (codeMat 92) (codeMat 254) (codeMat 443) false
    det92 det254 inv254
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1070_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1070_orbit
  simpa only [lower17] using h

theorem space1071_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 323), (131, 391), (64, 390), (34, 280), (19, 440), (10, 112), (7, 128)]
    (codeMat 93) (codeMat 254) (codeMat 443) false
    det93 det254 inv254
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1071_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1071_orbit
  simpa only [lower17] using h

theorem space1072_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 91), (129, 502), (64, 63), (34, 408), (19, 112), (10, 440), (7, 128)]
    (codeMat 86) (codeMat 253) (codeMat 415) false
    det86 det253 inv253
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1072_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1072_orbit
  simpa only [lower17] using h

theorem space1073_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 130, 67, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 3), (130, 438), (67, 274), (19, 404), (10, 306), (6, 45)]
    (codeMat 318) (codeMat 244) (codeMat 95) false
    det318 det244 inv244
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1073_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 130, 67, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1073_orbit
  simpa only [lower55] using h

theorem space1074_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 129, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 1), (129, 274), (64, 438), (19, 306), (10, 404), (6, 45)]
    (codeMat 382) (codeMat 204) (codeMat 114) false
    det382 det204 inv204
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1074_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 129, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1074_orbit
  simpa only [lower55] using h

theorem space1075_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 68), (130, 390), (64, 1), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 92) (codeMat 401) (codeMat 401) false
    det92 det401 inv401
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1075_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1075_orbit
  simpa only [lower17] using h

theorem space1076_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [385, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(385, 12), (64, 45), (32, 438), (19, 166), (10, 306), (6, 32)]
    (codeMat 93) (codeMat 431) (codeMat 477) true
    det93 det431 inv431
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1076_lower : 14 ≤ frozenWangTable.L0 (spanCodes [385, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1076_orbit
  simpa only [lower55] using h

theorem space1077_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [289, 129, 66, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(289, 44), (129, 164), (66, 274), (19, 166), (10, 306), (5, 45)]
    (codeMat 311) (codeMat 84) (codeMat 84) false
    det311 det84 inv84
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1077_lower : 14 ≤ frozenWangTable.L0 (spanCodes [289, 129, 66, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1077_orbit
  simpa only [lower55] using h

theorem space1078_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 91), (131, 502), (67, 457), (35, 280), (19, 112), (10, 456), (5, 128)]
    (codeMat 95) (codeMat 181) (codeMat 423) false
    det95 det181 inv181
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1078_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1078_orbit
  simpa only [lower17] using h

theorem space1079_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 130, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (130, 63), (67, 457), (35, 408), (19, 440), (10, 456), (5, 128)]
    (codeMat 87) (codeMat 183) (codeMat 419) false
    det87 det183 inv183
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1079_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1079_orbit
  simpa only [lower17] using h

theorem space1080_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [384, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(384, 3), (65, 45), (35, 304), (19, 306), (10, 404), (5, 438)]
    (codeMat 214) (codeMat 395) (codeMat 474) true
    det214 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1080_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1080_orbit
  simpa only [lower55] using h

theorem space1081_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 451), (131, 391), (64, 1), (35, 408), (19, 440), (10, 456), (5, 128)]
    (codeMat 84) (codeMat 183) (codeMat 419) false
    det84 det183 inv183
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1081_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1081_orbit
  simpa only [lower17] using h

theorem space1082_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 451), (130, 390), (64, 1), (35, 280), (19, 112), (10, 456), (5, 128)]
    (codeMat 92) (codeMat 181) (codeMat 423) false
    det92 det181 inv181
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1082_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1082_orbit
  simpa only [lower17] using h

theorem space1083_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 195, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (195, 45), (33, 436), (19, 306), (10, 166), (5, 438)]
    (codeMat 159) (codeMat 206) (codeMat 498) true
    det159 det206 inv206
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1083_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 195, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1083_orbit
  simpa only [lower55] using h

theorem space1084_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 130, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 228), (130, 63), (67, 502), (33, 160), (19, 440), (10, 112), (5, 128)]
    (codeMat 94) (codeMat 474) (codeMat 395) false
    det94 det474 inv474
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1084_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1084_orbit
  simpa only [lower17] using h

theorem space1085_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 69), (130, 390), (66, 391), (33, 488), (19, 112), (10, 440), (5, 128)]
    (codeMat 84) (codeMat 477) (codeMat 431) false
    det84 det477 inv477
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1085_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1085_orbit
  simpa only [lower17] using h

theorem space1086_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 68), (129, 391), (65, 390), (33, 160), (19, 440), (10, 112), (5, 128)]
    (codeMat 92) (codeMat 474) (codeMat 395) false
    det92 det474 inv474
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1086_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1086_orbit
  simpa only [lower17] using h

theorem space1087_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 429), (129, 502), (64, 63), (33, 488), (19, 112), (10, 440), (5, 128)]
    (codeMat 86) (codeMat 477) (codeMat 431) false
    det86 det477 inv477
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1087_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1087_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
