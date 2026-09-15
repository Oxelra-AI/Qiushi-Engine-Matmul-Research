import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1984_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 133, 64, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 326), (133, 324), (64, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 425) (codeMat 249) false
    det84 det425 inv425
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1984_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1984_orbit
  simpa only [lower10] using h

theorem space1985_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 64, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 70), (129, 68), (64, 1), (36, 432), (20, 416), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    det84 det417 inv417
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1985_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1985_orbit
  simpa only [lower10] using h

theorem space1986_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 129, 65, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 2), (129, 324), (65, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 161) (codeMat 161) false
    det85 det161 inv161
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1986_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 65, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space1986_orbit
  simpa only [lower10] using h

theorem space1987_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 160, 64, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 127), (160, 28), (64, 9), (17, 96), (8, 8), (5, 384), (2, 256)]
    (codeMat 86) (codeMat 421) (codeMat 179) false
    det86 det421 inv421
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1987_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 160, 64, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space1987_orbit
  simpa only [lower14] using h

theorem space1988_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 128, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 69), (128, 128), (32, 32), (17, 21), (8, 40), (5, 1), (2, 2)]
    (codeMat 273) (codeMat 337) (codeMat 337) false
    det273 det337 inv337
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1988_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 128, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space1988_orbit
  simpa only [lower11] using h

theorem space1989_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 64, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (129, 69), (64, 1), (36, 24), (20, 424), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 167) (codeMat 167) false
    det92 det167 inv167
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1989_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1989_orbit
  simpa only [lower10] using h

theorem space1990_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 64, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 360), (132, 363), (64, 1), (37, 97), (20, 235), (9, 8), (3, 511)]
    (codeMat 412) (codeMat 405) (codeMat 407) false
    det412 det405 inv405
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1990_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1990_orbit
  simpa only [lower14] using h

theorem space1991_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 132, 69, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 119), (132, 483), (69, 126), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 214) (codeMat 382) (codeMat 499) false
    det214 det382 inv382
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1991_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 132, 69, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1991_orbit
  simpa only [lower14] using h

theorem space1992_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 65, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (133, 71), (65, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 415) (codeMat 253) false
    det93 det415 inv415
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1992_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1992_orbit
  simpa only [lower10] using h

theorem space1993_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 128, 65, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 71), (128, 325), (65, 1), (33, 440), (20, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 423) (codeMat 181) false
    det93 det423 inv423
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1993_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1993_orbit
  simpa only [lower10] using h

theorem space1994_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 160, 64, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 118), (160, 413), (64, 9), (16, 360), (9, 8), (4, 384), (3, 256)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    det95 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1994_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 160, 64, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1994_orbit
  simpa only [lower14] using h

theorem space1995_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 193, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 248), (193, 120), (32, 3), (17, 62), (9, 63), (5, 32), (3, 8)]
    (codeMat 266) (codeMat 253) (codeMat 415) false
    det266 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1995_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 193, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1995_orbit
  simpa only [lower11] using h

theorem space1996_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 128, 66, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 69), (128, 1), (66, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    det92 det335 inv335
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1996_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1996_orbit
  simpa only [lower10] using h

theorem space1997_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 65, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 327), (128, 3), (65, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 92) (codeMat 375) (codeMat 491) false
    det92 det375 inv375
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1997_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1997_orbit
  simpa only [lower10] using h

theorem space1998_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 129, 66, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 258), (129, 70), (66, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    det85 det249 inv249
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1998_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1998_orbit
  simpa only [lower10] using h

theorem space1999_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 131, 64, 32, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    det85 det241 inv241
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1999_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 32, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space1999_orbit
  simpa only [lower10] using h

theorem space2000_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 67, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 130), (130, 1), (67, 70), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 85) (codeMat 106) (codeMat 396) false
    det85 det106 inv106
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2000_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2000_orbit
  simpa only [lower11] using h

theorem space2001_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 65, 34, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 210), (130, 9), (65, 54), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 87) (codeMat 106) (codeMat 396) false
    det87 det106 inv106
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2001_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 34, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2001_orbit
  simpa only [lower11] using h

theorem space2002_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 65, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 80), (128, 216), (65, 32), (32, 2), (16, 3), (10, 196), (4, 128)]
    (codeMat 106) (codeMat 114) (codeMat 204) false
    det106 det114 inv114
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2002_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space2002_orbit
  simpa only [lower11] using h

theorem space2003_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 133, 65, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (133, 327), (65, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 159) (codeMat 230) false
    det93 det159 inv159
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2003_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space2003_orbit
  simpa only [lower10] using h

theorem space2004_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [261, 133, 69, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(261, 198), (133, 199), (69, 197), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 92) (codeMat 499) (codeMat 382) false
    det92 det499 inv499
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2004_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2004_orbit
  simpa only [lower11] using h

theorem space2005_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 132, 69, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 9), (132, 210), (69, 100), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 84) (codeMat 84) false
    det87 det84 inv84
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2005_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2005_orbit
  simpa only [lower11] using h

theorem space2006_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 133, 64, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (133, 68), (64, 3), (32, 16), (20, 160), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    det84 det169 inv169
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2006_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space2006_orbit
  simpa only [lower10] using h

theorem space2007_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [289, 129, 64, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(289, 22), (129, 81), (64, 130), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 142) (codeMat 298) (codeMat 270) false
    det142 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2007_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 129, 64, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2007_orbit
  simpa only [lower11] using h

theorem space2008_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 192, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (192, 128), (33, 43), (17, 20), (8, 54), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 236) (codeMat 123) false
    det267 det236 inv236
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2008_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 192, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2008_orbit
  simpa only [lower11] using h

theorem space2009_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [321, 129, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(321, 248), (129, 120), (33, 28), (16, 9), (8, 63), (4, 32), (2, 8)]
    (codeMat 267) (codeMat 331) (codeMat 410) false
    det267 det331 inv331
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2009_lower : 12 ≤ frozenWangTable.L0 (spanCodes [321, 129, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2009_orbit
  simpa only [lower11] using h

theorem space2010_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 134, 64, 38, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 30), (134, 29), (64, 1), (38, 414), (20, 373), (10, 105), (1, 8)]
    (codeMat 396) (codeMat 419) (codeMat 183) false
    det396 det419 inv419
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2010_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 38, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2010_orbit
  simpa only [lower14] using h

theorem space2011_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 130, 66, 32, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 480), (130, 256), (66, 104), (32, 511), (20, 284), (10, 105), (1, 8)]
    (codeMat 334) (codeMat 421) (codeMat 179) false
    det334 det421 inv421
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2011_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 66, 32, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2011_orbit
  simpa only [lower14] using h

theorem space2012_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [290, 160, 98, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(290, 387), (160, 373), (98, 124), (18, 360), (10, 352), (6, 384), (1, 256)]
    (codeMat 87) (codeMat 230) (codeMat 159) false
    det87 det230 inv230
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2012_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 160, 98, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2012_orbit
  simpa only [lower14] using h

theorem space2013_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 162, 64, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 3), (162, 228), (64, 2), (16, 256), (10, 160), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    det140 det172 inv172
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2013_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 162, 64, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2013_orbit
  simpa only [lower10] using h

theorem space2014_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [288, 128, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(288, 32), (128, 216), (68, 148), (20, 196), (8, 128), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 282) (codeMat 267) false
    det177 det282 inv282
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2014_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 128, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2014_orbit
  simpa only [lower11] using h

theorem space2015_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(260, 455), (132, 454), (68, 452), (36, 504), (20, 496), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    det84 det500 inv500
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2015_lower : 9 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2015_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
