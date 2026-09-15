import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0960_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 450), (128, 1), (67, 391), (34, 208), (19, 456), (10, 440), (4, 128)]
    (codeMat 92) (codeMat 107) (codeMat 428) false
    det92 det107 inv107
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0960_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0960_orbit
  simpa only [lower17] using h

theorem space0961_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 402), (129, 502), (64, 63), (35, 80), (19, 112), (10, 440), (4, 128)]
    (codeMat 86) (codeMat 249) (codeMat 425) false
    det86 det249 inv249
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0961_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0961_orbit
  simpa only [lower17] using h

theorem space0962_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 129, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 3), (129, 274), (64, 438), (19, 306), (10, 404), (5, 45)]
    (codeMat 382) (codeMat 236) (codeMat 123) false
    det382 det236 inv236
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0962_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 129, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0962_orbit
  simpa only [lower55] using h

theorem space0963_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [290, 129, 66, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(290, 35), (129, 274), (66, 164), (19, 306), (10, 166), (5, 45)]
    (codeMat 318) (codeMat 428) (codeMat 107) false
    det318 det428 inv428
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0963_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 129, 66, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0963_orbit
  simpa only [lower55] using h

theorem space0964_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 196), (130, 1), (64, 390), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 85) (codeMat 330) (codeMat 394) false
    det85 det330 inv330
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0964_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0964_orbit
  simpa only [lower17] using h

theorem space0965_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 69), (128, 1), (67, 391), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    det92 det335 inv335
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0965_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0965_orbit
  simpa only [lower17] using h

theorem space0966_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 408), (64, 45), (35, 134), (19, 166), (10, 404), (5, 438)]
    (codeMat 158) (codeMat 409) (codeMat 473) true
    det158 det409 inv409
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0966_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0966_orbit
  simpa only [lower55] using h

theorem space0967_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 100), (129, 502), (64, 63), (32, 32), (19, 112), (10, 440), (6, 128)]
    (codeMat 86) (codeMat 473) (codeMat 409) false
    det86 det473 inv473
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0967_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0967_orbit
  simpa only [lower17] using h

theorem space0968_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 197), (131, 391), (64, 390), (32, 360), (19, 440), (10, 112), (6, 128)]
    (codeMat 93) (codeMat 478) (codeMat 445) false
    det93 det478 inv478
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0968_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0968_orbit
  simpa only [lower17] using h

theorem space0969_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 196), (128, 390), (67, 391), (32, 32), (19, 112), (10, 440), (6, 128)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    det85 det473 inv473
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0969_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0969_orbit
  simpa only [lower17] using h

theorem space0970_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 301), (130, 63), (67, 502), (32, 360), (19, 440), (10, 112), (6, 128)]
    (codeMat 94) (codeMat 478) (codeMat 445) false
    det94 det478 inv478
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0970_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0970_orbit
  simpa only [lower17] using h

theorem space0971_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 91), (129, 457), (64, 63), (33, 280), (19, 456), (10, 440), (6, 128)]
    (codeMat 95) (codeMat 111) (codeMat 412) false
    det95 det111 inv111
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0971_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0971_orbit
  simpa only [lower17] using h

theorem space0972_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 64, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 323), (130, 1), (64, 390), (33, 408), (19, 456), (10, 112), (6, 128)]
    (codeMat 85) (codeMat 110) (codeMat 444) false
    det85 det110 inv110
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0972_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0972_orbit
  simpa only [lower17] using h

theorem space0973_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 133), (65, 45), (33, 274), (19, 404), (10, 166), (6, 2)]
    (codeMat 143) (codeMat 395) (codeMat 474) true
    det143 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0973_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0973_orbit
  simpa only [lower55] using h

theorem space0974_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (129, 457), (66, 502), (33, 408), (19, 456), (10, 112), (6, 128)]
    (codeMat 87) (codeMat 110) (codeMat 444) false
    det87 det110 inv110
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0974_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0974_orbit
  simpa only [lower17] using h

theorem space0975_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 66, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 323), (130, 1), (66, 391), (33, 280), (19, 456), (10, 440), (6, 128)]
    (codeMat 93) (codeMat 111) (codeMat 412) false
    det93 det111 inv111
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0975_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0975_orbit
  simpa only [lower17] using h

theorem space0976_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 228), (129, 502), (66, 457), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 94) (codeMat 401) (codeMat 401) false
    det94 det401 inv401
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0976_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0976_orbit
  simpa only [lower17] using h

theorem space0977_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 301), (130, 63), (67, 457), (34, 488), (19, 440), (10, 456), (6, 128)]
    (codeMat 87) (codeMat 407) (codeMat 405) false
    det87 det407 inv407
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0977_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space0977_orbit
  simpa only [lower17] using h

theorem space0978_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 69), (130, 390), (64, 1), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 92) (codeMat 405) (codeMat 407) false
    det92 det405 inv405
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0978_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0978_orbit
  simpa only [lower17] using h

theorem space0979_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 197), (128, 390), (65, 1), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 93) (codeMat 405) (codeMat 407) false
    det93 det405 inv405
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0979_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0979_orbit
  simpa only [lower17] using h

theorem space0980_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 100), (128, 63), (66, 457), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 86) (codeMat 403) (codeMat 403) false
    det86 det403 inv403
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0980_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0980_orbit
  simpa only [lower17] using h

theorem space0981_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 130, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 228), (130, 63), (67, 457), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 87) (codeMat 403) (codeMat 403) false
    det87 det403 inv403
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0981_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0981_orbit
  simpa only [lower17] using h

theorem space0982_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [385, 64, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(385, 33), (64, 45), (34, 132), (19, 166), (10, 306), (7, 32)]
    (codeMat 93) (codeMat 395) (codeMat 474) true
    det93 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0982_lower : 14 ≤ frozenWangTable.L0 (spanCodes [385, 64, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0982_orbit
  simpa only [lower55] using h

theorem space0983_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 91), (128, 63), (66, 502), (34, 280), (19, 440), (10, 112), (7, 128)]
    (codeMat 95) (codeMat 254) (codeMat 443) false
    det95 det254 inv254
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0983_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0983_orbit
  simpa only [lower17] using h

theorem space0984_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 451), (130, 390), (66, 391), (34, 408), (19, 112), (10, 440), (7, 128)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    det84 det253 inv253
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0984_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0984_orbit
  simpa only [lower17] using h

theorem space0985_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 323), (128, 390), (67, 391), (34, 408), (19, 112), (10, 440), (7, 128)]
    (codeMat 85) (codeMat 253) (codeMat 415) false
    det85 det253 inv253
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0985_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0985_orbit
  simpa only [lower17] using h

theorem space0986_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 130, 67, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (130, 63), (67, 502), (34, 280), (19, 440), (10, 112), (7, 128)]
    (codeMat 94) (codeMat 254) (codeMat 443) false
    det94 det254 inv254
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0986_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space0986_orbit
  simpa only [lower17] using h

theorem space0987_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 128, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 437), (128, 438), (67, 436), (32, 45), (19, 166), (10, 404)]
    (codeMat 445) (codeMat 468) (codeMat 87) false
    det445 det468 inv468
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0987_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 128, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0987_orbit
  simpa only [lower55] using h

theorem space0988_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [289, 129, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(289, 46), (129, 164), (64, 438), (19, 166), (10, 404), (5, 45)]
    (codeMat 375) (codeMat 124) (codeMat 124) false
    det375 det124 inv124
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0988_lower : 14 ≤ frozenWangTable.L0 (spanCodes [289, 129, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0988_orbit
  simpa only [lower55] using h

theorem space0989_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 193, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (193, 441), (33, 436), (19, 306), (10, 166), (5, 438)]
    (codeMat 156) (codeMat 206) (codeMat 498) true
    det156 det206 inv206
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0989_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 193, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0989_orbit
  simpa only [lower55] using h

theorem space0990_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 131, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 301), (131, 502), (65, 63), (33, 488), (19, 112), (10, 440), (5, 128)]
    (codeMat 87) (codeMat 477) (codeMat 431) false
    det87 det477 inv477
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0990_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0990_orbit
  simpa only [lower17] using h

theorem space0991_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 196), (131, 391), (64, 390), (33, 160), (19, 440), (10, 112), (5, 128)]
    (codeMat 93) (codeMat 474) (codeMat 395) false
    det93 det474 inv474
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0991_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0991_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
