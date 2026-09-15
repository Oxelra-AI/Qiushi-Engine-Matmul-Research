import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1920_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 131, 67, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 496), (131, 160), (67, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 354) (codeMat 212) (codeMat 86) false
    det354 det212 inv212
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1920_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 131, 67, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1920_orbit
  simpa only [lower65] using h

theorem space1921_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 129, 65, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 496), (129, 336), (65, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 298) (codeMat 158) (codeMat 358) false
    det298 det158 inv158
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1921_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 129, 65, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1921_orbit
  simpa only [lower65] using h

theorem space1922_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [261, 194, 33, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(261, 495), (194, 493), (33, 463), (20, 440), (10, 118)]
    (codeMat 491) (codeMat 233) (codeMat 233) true
    det491 det233 inv233
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1922_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 194, 33, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1922_orbit
  simpa only [lower144] using h

theorem space1923_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [291, 162, 99, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(291, 261), (162, 186), (99, 286), (16, 16), (10, 176), (4, 320)]
    (codeMat 86) (codeMat 348) (codeMat 125) false
    det86 det348 inv348
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1923_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 162, 99, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1923_orbit
  simpa only [lower65] using h

theorem space1924_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 162, 65, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 261), (162, 170), (65, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    det84 det340 inv340
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1924_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 65, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1924_orbit
  simpa only [lower65] using h

theorem space1925_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 162, 64, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 321), (162, 78), (64, 260), (17, 176), (10, 160), (5, 320)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    det93 det212 inv212
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1925_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 64, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space1925_orbit
  simpa only [lower65] using h

theorem space1926_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 129, 97, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 260), (129, 186), (97, 69), (20, 160), (8, 320), (2, 16)]
    (codeMat 143) (codeMat 337) (codeMat 337) false
    det143 det337 inv337
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1926_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 97, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space1926_orbit
  simpa only [lower65] using h

theorem space1927_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [292, 165, 100, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(292, 1), (165, 431), (100, 261), (20, 496), (9, 320), (3, 16)]
    (codeMat 207) (codeMat 215) (codeMat 342) false
    det207 det215 inv215
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1927_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 165, 100, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space1927_orbit
  simpa only [lower65] using h

theorem space1928_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 69, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 148), (128, 128), (69, 150), (39, 252), (20, 224), (10, 255)]
    (codeMat 103) (codeMat 489) (codeMat 241) true
    det103 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1928_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1928_orbit
  simpa only [lower35] using h

theorem space1929_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 134, 65, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 176), (134, 480), (65, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 355) (codeMat 339) (codeMat 467) false
    det355 det339 inv339
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1929_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 65, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1929_orbit
  simpa only [lower65] using h

theorem space1930_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 69, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (130, 3), (69, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 213) (codeMat 122) (codeMat 460) false
    det213 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1930_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 69, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1930_orbit
  simpa only [lower35] using h

theorem space1931_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 69, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (134, 22), (69, 148), (32, 3), (20, 31), (10, 252)]
    (codeMat 111) (codeMat 94) (codeMat 500) true
    det111 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1931_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 69, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1931_orbit
  simpa only [lower35] using h

theorem space1932_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 135, 66, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 496), (135, 336), (66, 480), (32, 1), (20, 79), (10, 507)]
    (codeMat 354) (codeMat 159) (codeMat 230) false
    det354 det159 inv159
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1932_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1932_orbit
  simpa only [lower65] using h

theorem space1933_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [290, 162, 98, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(290, 246), (162, 245), (98, 244), (17, 104), (10, 96), (5, 128)]
    (codeMat 92) (codeMat 482) (codeMat 143) false
    det92 det482 inv482
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1933_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 162, 98, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space1933_orbit
  simpa only [lower35] using h

theorem space1934_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [289, 132, 65, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(289, 22), (132, 235), (65, 130), (20, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 314) (codeMat 271) false
    det206 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1934_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 132, 65, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space1934_orbit
  simpa only [lower35] using h

theorem space1935_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [289, 132, 64, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(289, 20), (132, 97), (64, 130), (20, 96), (8, 128), (2, 8)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    det142 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1935_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 132, 64, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space1935_orbit
  simpa only [lower35] using h

theorem space1936_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 166, 68, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 27), (166, 228), (68, 11), (20, 507), (10, 79), (1, 1)]
    (codeMat 417) (codeMat 183) (codeMat 419) false
    det417 det183 inv183
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1936_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 166, 68, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1936_orbit
  simpa only [lower65] using h

theorem space1937_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [290, 134, 66, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(290, 139), (134, 245), (66, 29), (20, 252), (10, 31), (1, 3)]
    (codeMat 183) (codeMat 307) (codeMat 311) true
    det183 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1937_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 134, 66, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1937_orbit
  simpa only [lower35] using h

theorem space1938_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 69, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 263), (129, 262), (69, 196), (37, 312), (20, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 500) (codeMat 94) false
    det92 det500 inv500
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1938_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 69, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space1938_orbit
  simpa only [lower17] using h

theorem space1939_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [262, 132, 68, 36, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(262, 100), (132, 329), (68, 402), (36, 32), (20, 328), (10, 208), (1, 128)]
    (codeMat 94) (codeMat 266) (codeMat 266) false
    det94 det266 inv266
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space1939_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 132, 68, 36, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space1939_orbit
  simpa only [lower17] using h

theorem space1940_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 64, 32, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 68), (64, 128), (32, 8), (16, 32), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    det273 det140 inv140
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1940_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1940_orbit
  simpa only [lower11] using h

theorem space1941_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 28), (128, 2), (64, 3), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 140) (codeMat 281) (codeMat 281) false
    det140 det281 inv281
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1941_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1941_orbit
  simpa only [lower11] using h

theorem space1942_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 161, 64, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 502), (161, 501), (64, 1), (16, 360), (9, 8), (4, 384), (3, 256)]
    (codeMat 92) (codeMat 419) (codeMat 183) false
    det92 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1942_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 161, 64, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1942_orbit
  simpa only [lower14] using h

theorem space1943_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 133, 65, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 2), (133, 324), (65, 3), (32, 16), (20, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 169) (codeMat 225) false
    det85 det169 inv169
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1943_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1943_orbit
  simpa only [lower10] using h

theorem space1944_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 64, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 71), (129, 69), (64, 1), (33, 440), (20, 168), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 423) (codeMat 181) false
    det92 det423 inv423
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1944_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1944_orbit
  simpa only [lower10] using h

theorem space1945_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 64, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 327), (64, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 415) (codeMat 253) false
    det92 det415 inv415
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1945_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1945_orbit
  simpa only [lower10] using h

theorem space1946_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 68, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 511), (128, 3), (68, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 382) (codeMat 499) false
    det212 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1946_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1946_orbit
  simpa only [lower14] using h

theorem space1947_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 132, 68, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 198), (132, 71), (68, 197), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 93) (codeMat 499) (codeMat 382) false
    det93 det499 inv499
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1947_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1947_orbit
  simpa only [lower11] using h

theorem space1948_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 132, 64, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (132, 71), (64, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 159) (codeMat 230) false
    det92 det159 inv159
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1948_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1948_orbit
  simpa only [lower10] using h

theorem space1949_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 64, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 361), (133, 362), (64, 1), (33, 105), (20, 284), (8, 8), (2, 511)]
    (codeMat 468) (codeMat 403) (codeMat 403) false
    det468 det403 inv403
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1949_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1949_orbit
  simpa only [lower14] using h

theorem space1950_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 132, 69, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 483), (132, 278), (69, 252), (33, 227), (20, 406), (8, 511), (2, 130)]
    (codeMat 415) (codeMat 345) (codeMat 345) false
    det415 det345 inv345
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1950_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 69, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1950_orbit
  simpa only [lower14] using h

theorem space1951_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 64, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (129, 68), (64, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    det84 det161 inv161
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1951_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1951_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
