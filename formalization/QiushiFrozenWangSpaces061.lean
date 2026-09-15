import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1952_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 129, 65, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 70), (129, 324), (65, 1), (36, 432), (20, 416), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 417) (codeMat 177) false
    det85 det417 inv417
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1952_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1952_orbit
  simpa only [lower10] using h

theorem space1953_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 133, 65, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 326), (133, 68), (65, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 425) (codeMat 249) false
    det85 det425 inv425
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1953_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1953_orbit
  simpa only [lower10] using h

theorem space1954_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 82), (128, 9), (64, 54), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 86) (codeMat 106) (codeMat 396) false
    det86 det106 inv106
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1954_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space1954_orbit
  simpa only [lower11] using h

theorem space1955_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 65, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    det92 det215 inv215
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1955_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space1955_orbit
  simpa only [lower10] using h

theorem space1956_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 130, 66, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (130, 325), (66, 327), (33, 280), (17, 168), (10, 184), (5, 256)]
    (codeMat 92) (codeMat 239) (codeMat 351) false
    det92 det239 inv239
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1956_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space1956_orbit
  simpa only [lower10] using h

theorem space1957_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (130, 3), (64, 256), (35, 503), (17, 284), (10, 227), (5, 130)]
    (codeMat 277) (codeMat 370) (codeMat 207) false
    det277 det370 inv370
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1957_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1957_orbit
  simpa only [lower14] using h

theorem space1958_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 66, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 119), (131, 287), (66, 483), (35, 503), (17, 284), (10, 227), (5, 130)]
    (codeMat 407) (codeMat 370) (codeMat 207) false
    det407 det370 inv370
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1958_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 66, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1958_orbit
  simpa only [lower14] using h

theorem space1959_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 21), (130, 3), (67, 28), (35, 381), (17, 227), (10, 284), (5, 8)]
    (codeMat 461) (codeMat 342) (codeMat 215) false
    det461 det342 inv342
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1959_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1959_orbit
  simpa only [lower14] using h

theorem space1960_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 64, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 9), (130, 219), (64, 54), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    det86 det94 inv94
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1960_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space1960_orbit
  simpa only [lower11] using h

theorem space1961_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    det84 det94 inv94
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1961_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space1961_orbit
  simpa only [lower11] using h

theorem space1962_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 67, 33, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (131, 31), (67, 28), (33, 105), (16, 511), (10, 284), (4, 8)]
    (codeMat 460) (codeMat 214) (codeMat 214) false
    det460 det214 inv214
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1962_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 33, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1962_orbit
  simpa only [lower14] using h

theorem space1963_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 65, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 208), (130, 8), (65, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 106) (codeMat 98) (codeMat 140) false
    det106 det98 inv98
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1963_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space1963_orbit
  simpa only [lower11] using h

theorem space1964_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 67, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 80), (128, 216), (67, 240), (32, 2), (16, 3), (10, 198), (4, 128)]
    (codeMat 106) (codeMat 122) (codeMat 460) false
    det106 det122 inv122
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1964_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space1964_orbit
  simpa only [lower11] using h

theorem space1965_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 64, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 68), (130, 2), (64, 325), (34, 160), (16, 16), (10, 168), (4, 256)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    det85 det337 inv337
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1965_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space1965_orbit
  simpa only [lower10] using h

theorem space1966_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 66, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (129, 28), (66, 31), (34, 96), (16, 256), (10, 480), (4, 8)]
    (codeMat 141) (codeMat 205) (codeMat 242) false
    det141 det205 inv205
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1966_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 66, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1966_orbit
  simpa only [lower14] using h

theorem space1967_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 66, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 68), (130, 2), (66, 327), (34, 160), (16, 16), (10, 184), (4, 256)]
    (codeMat 85) (codeMat 345) (codeMat 345) false
    det85 det345 inv345
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1967_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space1967_orbit
  simpa only [lower10] using h

theorem space1968_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 67, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 129), (130, 3), (67, 198), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 85) (codeMat 94) (codeMat 500) false
    det85 det94 inv94
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1968_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space1968_orbit
  simpa only [lower11] using h

theorem space1969_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 131, 67, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (131, 70), (67, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 84) (codeMat 249) (codeMat 425) false
    det84 det249 inv249
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1969_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1969_orbit
  simpa only [lower10] using h

theorem space1970_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 65, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (129, 326), (65, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    det84 det241 inv241
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1970_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1970_orbit
  simpa only [lower10] using h

theorem space1971_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 130, 67, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (130, 1), (67, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 93) (codeMat 335) (codeMat 426) false
    det93 det335 inv335
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1971_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1971_orbit
  simpa only [lower10] using h

theorem space1972_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 64, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 71), (130, 3), (64, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 93) (codeMat 375) (codeMat 491) false
    det93 det375 inv375
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1972_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1972_orbit
  simpa only [lower10] using h

theorem space1973_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 128, 67, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 324), (128, 2), (67, 327), (34, 160), (16, 16), (10, 184), (4, 256)]
    (codeMat 84) (codeMat 345) (codeMat 345) false
    det84 det345 inv345
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1973_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space1973_orbit
  simpa only [lower10] using h

theorem space1974_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 97), (131, 284), (65, 511), (34, 96), (16, 256), (10, 480), (4, 8)]
    (codeMat 142) (codeMat 205) (codeMat 242) false
    det142 det205 inv205
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1974_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1974_orbit
  simpa only [lower14] using h

theorem space1975_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 65, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 324), (128, 2), (65, 325), (34, 160), (16, 16), (10, 168), (4, 256)]
    (codeMat 84) (codeMat 337) (codeMat 337) false
    det84 det337 inv337
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1975_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space1975_orbit
  simpa only [lower10] using h

theorem space1976_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 64, 33, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 118), (128, 128), (64, 256), (33, 227), (16, 130), (10, 406), (4, 511)]
    (codeMat 286) (codeMat 372) (codeMat 93) false
    det286 det372 inv372
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1976_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 33, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1976_orbit
  simpa only [lower14] using h

theorem space1977_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 33, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (131, 480), (65, 256), (33, 105), (16, 511), (10, 284), (4, 8)]
    (codeMat 334) (codeMat 214) (codeMat 214) false
    det334 det214 inv214
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1977_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1977_orbit
  simpa only [lower14] using h

theorem space1978_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 65, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 240), (130, 40), (65, 32), (34, 198), (17, 69), (10, 68), (5, 128)]
    (codeMat 107) (codeMat 482) (codeMat 143) false
    det107 det482 inv482
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1978_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space1978_orbit
  simpa only [lower11] using h

theorem space1979_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 352), (129, 224), (64, 256), (35, 381), (17, 227), (10, 284), (5, 8)]
    (codeMat 270) (codeMat 342) (codeMat 215) false
    det270 det342 inv342
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1979_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1979_orbit
  simpa only [lower14] using h

theorem space1980_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 65, 35, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 137), (130, 384), (65, 256), (35, 138), (17, 276), (10, 406), (5, 511)]
    (codeMat 342) (codeMat 244) (codeMat 95) false
    det342 det244 inv244
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1980_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 35, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1980_orbit
  simpa only [lower14] using h

theorem space1981_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 67, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 259), (128, 325), (67, 327), (33, 280), (17, 168), (10, 184), (5, 256)]
    (codeMat 93) (codeMat 239) (codeMat 351) false
    det93 det239 inv239
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1981_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space1981_orbit
  simpa only [lower10] using h

theorem space1982_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 131, 64, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 257), (131, 327), (64, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 93) (codeMat 215) (codeMat 342) false
    det93 det215 inv215
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1982_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space1982_orbit
  simpa only [lower10] using h

theorem space1983_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 33, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 406), (129, 227), (64, 511), (33, 392), (17, 224), (10, 480), (5, 8)]
    (codeMat 206) (codeMat 379) (codeMat 247) false
    det206 det379 inv379
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1983_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 33, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1983_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
