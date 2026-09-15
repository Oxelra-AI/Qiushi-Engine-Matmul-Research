import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1024_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 135), (64, 45), (33, 274), (19, 404), (10, 166), (6, 2)]
    (codeMat 142) (codeMat 395) (codeMat 474) true
    det142 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1024_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1024_orbit
  simpa only [lower55] using h

theorem space1025_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 451), (128, 1), (67, 391), (33, 280), (19, 456), (10, 440), (6, 128)]
    (codeMat 92) (codeMat 111) (codeMat 412) false
    det92 det111 inv111
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1025_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1025_orbit
  simpa only [lower17] using h

theorem space1026_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [384, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(384, 1), (66, 139), (33, 274), (19, 404), (10, 166), (6, 2)]
    (codeMat 140) (codeMat 395) (codeMat 474) true
    det140 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1026_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1026_orbit
  simpa only [lower55] using h

theorem space1027_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 69), (129, 391), (65, 390), (32, 360), (19, 440), (10, 112), (6, 128)]
    (codeMat 92) (codeMat 478) (codeMat 445) false
    det92 det478 inv478
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1027_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1027_orbit
  simpa only [lower17] using h

theorem space1028_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 65, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 228), (131, 502), (65, 63), (32, 32), (19, 112), (10, 440), (6, 128)]
    (codeMat 87) (codeMat 473) (codeMat 409) false
    det87 det473 inv473
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1028_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1028_orbit
  simpa only [lower17] using h

theorem space1029_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [387, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(387, 135), (64, 45), (32, 438), (19, 306), (10, 166), (6, 2)]
    (codeMat 207) (codeMat 445) (codeMat 478) true
    det207 det445 inv445
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1029_lower : 14 ≤ frozenWangTable.L0 (spanCodes [387, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1029_orbit
  simpa only [lower55] using h

theorem space1030_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 429), (128, 63), (66, 502), (32, 360), (19, 440), (10, 112), (6, 128)]
    (codeMat 95) (codeMat 478) (codeMat 445) false
    det95 det478 inv478
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1030_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1030_orbit
  simpa only [lower17] using h

theorem space1031_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 68), (130, 390), (66, 391), (32, 32), (19, 112), (10, 440), (6, 128)]
    (codeMat 84) (codeMat 473) (codeMat 409) false
    det84 det473 inv473
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1031_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1031_orbit
  simpa only [lower17] using h

theorem space1032_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 100), (131, 502), (67, 457), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 95) (codeMat 401) (codeMat 401) false
    det95 det401 inv401
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1032_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1032_orbit
  simpa only [lower17] using h

theorem space1033_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 429), (128, 63), (66, 457), (34, 488), (19, 440), (10, 456), (6, 128)]
    (codeMat 86) (codeMat 407) (codeMat 405) false
    det86 det407 inv407
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1033_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1033_orbit
  simpa only [lower17] using h

theorem space1034_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 131, 67, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 168), (131, 272), (67, 304), (39, 287), (19, 166), (10, 306)]
    (codeMat 359) (codeMat 444) (codeMat 110) false
    det359 det444 inv444
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1034_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1034_orbit
  simpa only [lower55] using h

theorem space1035_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 129, 65, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 170), (129, 406), (65, 438), (36, 45), (19, 404), (10, 306)]
    (codeMat 423) (codeMat 348) (codeMat 125) false
    det423 det348 inv348
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1035_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1035_orbit
  simpa only [lower55] using h

theorem space1036_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 130, 67, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 168), (130, 32), (67, 304), (34, 287), (19, 404), (10, 306)]
    (codeMat 303) (codeMat 428) (codeMat 107) false
    det303 det428 inv428
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1036_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 130, 67, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1036_orbit
  simpa only [lower55] using h

theorem space1037_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [263, 130, 64, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(263, 138), (130, 32), (64, 438), (35, 139), (19, 166), (10, 306)]
    (codeMat 431) (codeMat 204) (codeMat 114) false
    det431 det204 inv204
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1037_lower : 14 ≤ frozenWangTable.L0 (spanCodes [263, 130, 64, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1037_orbit
  simpa only [lower55] using h

theorem space1038_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 129, 65, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 316), (129, 406), (65, 32), (35, 441), (19, 404), (10, 166)]
    (codeMat 431) (codeMat 372) (codeMat 93) false
    det431 det372 inv372
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1038_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1038_orbit
  simpa only [lower55] using h

theorem space1039_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [263, 130, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(263, 408), (130, 32), (67, 304), (32, 45), (19, 404), (10, 306)]
    (codeMat 303) (codeMat 396) (codeMat 106) false
    det303 det396 inv396
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1039_lower : 14 ≤ frozenWangTable.L0 (spanCodes [263, 130, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1039_orbit
  simpa only [lower55] using h

theorem space1040_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 128, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 170), (128, 438), (67, 406), (32, 45), (19, 306), (10, 404)]
    (codeMat 431) (codeMat 412) (codeMat 111) false
    det431 det412 inv412
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1040_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 128, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space1040_orbit
  simpa only [lower55] using h

theorem space1041_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [291, 129, 66, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(291, 14), (129, 164), (66, 274), (19, 166), (10, 306), (6, 45)]
    (codeMat 311) (codeMat 372) (codeMat 93) false
    det311 det372 inv372
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1041_lower : 14 ≤ frozenWangTable.L0 (spanCodes [291, 129, 66, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1041_orbit
  simpa only [lower55] using h

theorem space1042_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [290, 131, 65, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(290, 44), (131, 274), (65, 438), (19, 306), (10, 404), (6, 45)]
    (codeMat 311) (codeMat 204) (codeMat 114) false
    det311 det204 inv204
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1042_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 131, 65, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1042_orbit
  simpa only [lower55] using h

theorem space1043_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 69), (131, 391), (64, 1), (34, 488), (19, 440), (10, 456), (6, 128)]
    (codeMat 84) (codeMat 407) (codeMat 405) false
    det84 det407 inv407
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1043_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1043_orbit
  simpa only [lower17] using h

theorem space1044_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 196), (128, 390), (65, 1), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 93) (codeMat 401) (codeMat 401) false
    det93 det401 inv401
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1044_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1044_orbit
  simpa only [lower17] using h

theorem space1045_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 195, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 46), (195, 45), (32, 32), (19, 306), (10, 166), (6, 438)]
    (codeMat 159) (codeMat 234) (codeMat 461) true
    det159 det234 inv234
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1045_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 195, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1045_orbit
  simpa only [lower55] using h

theorem space1046_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [387, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(387, 170), (64, 45), (34, 272), (19, 306), (10, 166), (7, 2)]
    (codeMat 207) (codeMat 409) (codeMat 473) true
    det207 det409 inv409
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1046_lower : 14 ≤ frozenWangTable.L0 (spanCodes [387, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1046_orbit
  simpa only [lower55] using h

theorem space1047_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 192, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 170), (192, 45), (35, 34), (19, 404), (10, 306), (7, 2)]
    (codeMat 207) (codeMat 234) (codeMat 461) true
    det207 det234 inv234
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1047_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 192, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1047_orbit
  simpa only [lower55] using h

theorem space1048_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 170), (64, 45), (35, 436), (19, 404), (10, 166), (7, 2)]
    (codeMat 142) (codeMat 431) (codeMat 477) true
    det142 det431 inv431
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1048_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1048_orbit
  simpa only [lower55] using h

theorem space1049_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [321, 128, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(321, 170), (128, 45), (32, 438), (19, 166), (10, 404), (7, 2)]
    (codeMat 207) (codeMat 375) (codeMat 491) true
    det207 det375 inv375
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1049_lower : 14 ≤ frozenWangTable.L0 (spanCodes [321, 128, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1049_orbit
  simpa only [lower55] using h

theorem space1050_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [291, 129, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(291, 12), (129, 164), (64, 438), (19, 166), (10, 404), (4, 45)]
    (codeMat 375) (codeMat 348) (codeMat 125) false
    det375 det348 inv348
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1050_lower : 14 ≤ frozenWangTable.L0 (spanCodes [291, 129, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1050_orbit
  simpa only [lower55] using h

theorem space1051_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 450), (130, 390), (66, 391), (35, 80), (19, 112), (10, 440), (4, 128)]
    (codeMat 84) (codeMat 249) (codeMat 425) false
    det84 det249 inv249
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1051_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1051_orbit
  simpa only [lower17] using h

theorem space1052_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 322), (131, 391), (64, 390), (35, 208), (19, 440), (10, 112), (4, 128)]
    (codeMat 93) (codeMat 250) (codeMat 397) false
    det93 det250 inv250
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1052_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1052_orbit
  simpa only [lower17] using h

theorem space1053_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 193, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 316), (193, 287), (33, 304), (19, 166), (10, 404), (4, 32)]
    (codeMat 87) (codeMat 234) (codeMat 461) true
    det87 det234 inv234
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1053_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 193, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1053_orbit
  simpa only [lower55] using h

theorem space1054_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [387, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(387, 408), (64, 45), (33, 164), (19, 306), (10, 404), (4, 438)]
    (codeMat 215) (codeMat 431) (codeMat 477) true
    det215 det431 inv431
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1054_lower : 14 ≤ frozenWangTable.L0 (spanCodes [387, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1054_orbit
  simpa only [lower55] using h

theorem space1055_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [290, 130, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(290, 14), (130, 438), (67, 164), (19, 404), (10, 166), (5, 45)]
    (codeMat 311) (codeMat 444) (codeMat 110) false
    det311 det444 inv444
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1055_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 130, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1055_orbit
  simpa only [lower55] using h


end QiushiMatmul.FrozenWang
