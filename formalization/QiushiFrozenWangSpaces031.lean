import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0992_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 197), (128, 390), (67, 391), (33, 488), (19, 112), (10, 440), (5, 128)]
    (codeMat 85) (codeMat 477) (codeMat 431) false
    det85 det477 inv477
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0992_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0992_orbit
  simpa only [lower17] using h

theorem space0993_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 100), (128, 63), (66, 502), (33, 160), (19, 440), (10, 112), (5, 128)]
    (codeMat 95) (codeMat 474) (codeMat 395) false
    det95 det474 inv474
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0993_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0993_orbit
  simpa only [lower17] using h

theorem space0994_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 301), (131, 457), (65, 63), (32, 360), (19, 456), (10, 440), (5, 128)]
    (codeMat 94) (codeMat 335) (codeMat 426) false
    det94 det335 inv335
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0994_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0994_orbit
  simpa only [lower17] using h

theorem space0995_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 228), (129, 457), (66, 502), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 87) (codeMat 330) (codeMat 394) false
    det87 det330 inv330
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0995_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0995_orbit
  simpa only [lower17] using h

theorem space0996_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [321, 130, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(321, 133), (130, 45), (35, 272), (19, 166), (10, 404), (5, 2)]
    (codeMat 206) (codeMat 339) (codeMat 467) true
    det206 det339 inv339
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0996_lower : 14 ≤ frozenWangTable.L0 (spanCodes [321, 130, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0996_orbit
  simpa only [lower55] using h

theorem space0997_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 323), (129, 391), (65, 1), (35, 408), (19, 440), (10, 456), (5, 128)]
    (codeMat 85) (codeMat 183) (codeMat 419) false
    det85 det183 inv183
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0997_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0997_orbit
  simpa only [lower17] using h

theorem space0998_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 323), (128, 390), (65, 1), (35, 280), (19, 112), (10, 456), (5, 128)]
    (codeMat 93) (codeMat 181) (codeMat 423) false
    det93 det181 inv181
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0998_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space0998_orbit
  simpa only [lower17] using h

theorem space0999_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [387, 64, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(387, 437), (64, 45), (35, 304), (19, 306), (10, 404), (5, 438)]
    (codeMat 215) (codeMat 395) (codeMat 474) true
    det215 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0999_lower : 14 ≤ frozenWangTable.L0 (spanCodes [387, 64, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0999_orbit
  simpa only [lower55] using h

theorem space1000_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [384, 67, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(384, 1), (67, 441), (35, 304), (19, 306), (10, 404), (5, 438)]
    (codeMat 212) (codeMat 395) (codeMat 474) true
    det212 det395 inv395
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1000_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 67, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space1000_orbit
  simpa only [lower55] using h

theorem space1001_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (129, 502), (66, 457), (35, 280), (19, 112), (10, 456), (5, 128)]
    (codeMat 94) (codeMat 181) (codeMat 423) false
    det94 det181 inv181
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1001_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1001_orbit
  simpa only [lower17] using h

theorem space1002_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 91), (128, 63), (66, 457), (35, 408), (19, 440), (10, 456), (5, 128)]
    (codeMat 86) (codeMat 183) (codeMat 419) false
    det86 det183 inv183
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1002_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space1002_orbit
  simpa only [lower17] using h

theorem space1003_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [290, 129, 66, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(290, 33), (129, 274), (66, 164), (19, 306), (10, 166), (4, 45)]
    (codeMat 318) (codeMat 396) (codeMat 106) false
    det318 det396 inv396
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1003_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 129, 66, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1003_orbit
  simpa only [lower55] using h

theorem space1004_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [385, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(385, 46), (65, 45), (33, 164), (19, 306), (10, 404), (4, 438)]
    (codeMat 214) (codeMat 431) (codeMat 477) true
    det214 det431 inv431
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1004_lower : 14 ≤ frozenWangTable.L0 (spanCodes [385, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1004_orbit
  simpa only [lower55] using h

theorem space1005_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 450), (129, 391), (65, 390), (35, 208), (19, 440), (10, 112), (4, 128)]
    (codeMat 92) (codeMat 250) (codeMat 397) false
    det92 det250 inv250
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1005_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1005_orbit
  simpa only [lower17] using h

theorem space1006_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 322), (128, 390), (67, 391), (35, 80), (19, 112), (10, 440), (4, 128)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    det85 det249 inv249
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1006_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space1006_orbit
  simpa only [lower17] using h

theorem space1007_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [322, 129, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(322, 14), (129, 441), (34, 274), (19, 404), (10, 306), (4, 438)]
    (codeMat 157) (codeMat 375) (codeMat 491) true
    det157 det375 inv375
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1007_lower : 14 ≤ frozenWangTable.L0 (spanCodes [322, 129, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space1007_orbit
  simpa only [lower55] using h

theorem space1008_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [291, 129, 64, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(291, 44), (129, 164), (64, 438), (19, 166), (10, 404), (7, 45)]
    (codeMat 375) (codeMat 92) (codeMat 116) false
    det375 det92 inv92
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1008_lower : 14 ≤ frozenWangTable.L0 (spanCodes [291, 129, 64, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1008_orbit
  simpa only [lower55] using h

theorem space1009_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 128, 66, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 1), (128, 438), (66, 164), (19, 404), (10, 166), (7, 45)]
    (codeMat 382) (codeMat 156) (codeMat 102) false
    det382 det156 inv156
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1009_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 128, 66, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1009_orbit
  simpa only [lower55] using h

theorem space1010_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 196), (129, 391), (65, 1), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 85) (codeMat 403) (codeMat 403) false
    det85 det403 inv403
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1010_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1010_orbit
  simpa only [lower17] using h

theorem space1011_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 68), (131, 391), (64, 1), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 84) (codeMat 403) (codeMat 403) false
    det84 det403 inv403
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1011_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1011_orbit
  simpa only [lower17] using h

theorem space1012_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 67, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 429), (131, 502), (67, 457), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 95) (codeMat 405) (codeMat 407) false
    det95 det405 inv405
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1012_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1012_orbit
  simpa only [lower17] using h

theorem space1013_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 66, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 301), (129, 502), (66, 457), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 94) (codeMat 405) (codeMat 407) false
    det94 det405 inv405
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1013_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1013_orbit
  simpa only [lower17] using h

theorem space1014_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 193, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (193, 287), (35, 34), (19, 404), (10, 166), (7, 32)]
    (codeMat 95) (codeMat 213) (codeMat 470) true
    det95 det213 inv213
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1014_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 193, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1014_orbit
  simpa only [lower55] using h

theorem space1015_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [385, 64, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(385, 33), (64, 45), (35, 406), (19, 404), (10, 306), (7, 32)]
    (codeMat 85) (codeMat 445) (codeMat 478) true
    det85 det445 inv445
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1015_lower : 14 ≤ frozenWangTable.L0 (spanCodes [385, 64, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1015_orbit
  simpa only [lower55] using h

theorem space1016_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 128, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 68), (128, 1), (67, 391), (35, 160), (19, 456), (10, 440), (7, 128)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    det92 det331 inv331
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1016_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1016_orbit
  simpa only [lower17] using h

theorem space1017_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 429), (131, 457), (67, 502), (35, 488), (19, 456), (10, 112), (7, 128)]
    (codeMat 86) (codeMat 334) (codeMat 442) false
    det86 det334 inv334
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1017_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1017_orbit
  simpa only [lower17] using h

theorem space1018_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 301), (129, 457), (66, 502), (35, 488), (19, 456), (10, 112), (7, 128)]
    (codeMat 87) (codeMat 334) (codeMat 442) false
    det87 det334 inv334
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1018_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1018_orbit
  simpa only [lower17] using h

theorem space1019_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 130, 66, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 196), (130, 1), (66, 391), (35, 160), (19, 456), (10, 440), (7, 128)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    det93 det331 inv331
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1019_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space1019_orbit
  simpa only [lower17] using h

theorem space1020_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [386, 66, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(386, 136), (66, 139), (34, 272), (19, 306), (10, 166), (7, 2)]
    (codeMat 205) (codeMat 409) (codeMat 473) true
    det205 det409 inv409
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1020_lower : 14 ≤ frozenWangTable.L0 (spanCodes [386, 66, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space1020_orbit
  simpa only [lower55] using h

theorem space1021_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [288, 129, 66, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(288, 1), (129, 274), (66, 164), (19, 306), (10, 166), (6, 45)]
    (codeMat 318) (codeMat 140) (codeMat 98) false
    det318 det140 inv140
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space1021_lower : 14 ≤ frozenWangTable.L0 (spanCodes [288, 129, 66, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space1021_orbit
  simpa only [lower55] using h

theorem space1022_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 451), (128, 1), (65, 390), (33, 408), (19, 456), (10, 112), (6, 128)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    det84 det110 inv110
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1022_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1022_orbit
  simpa only [lower17] using h

theorem space1023_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 131, 65, 33, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (131, 457), (65, 63), (33, 280), (19, 456), (10, 440), (6, 128)]
    (codeMat 94) (codeMat 111) (codeMat 412) false
    det94 det111 inv111
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1023_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 33, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space1023_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
