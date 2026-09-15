import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4320_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 67, 32, 17, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 100), (131, 502), (67, 457), (32, 32), (17, 112), (11, 456), (6, 128)]
    (codeMat 86) (codeMat 401) (codeMat 401) false
    det86 det401 inv401
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4320_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 32, 17, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space4320_orbit
  simpa only [lower17] using h

theorem space4321_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [262, 134, 68, 36, 16, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(262, 69), (134, 68), (68, 322), (36, 360), (16, 32), (14, 80), (1, 128)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    det84 det396 inv396
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4321_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 134, 68, 36, 16, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space4321_orbit
  simpa only [lower17] using h

theorem space4322_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 130, 65, 33, 21, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 133), (130, 2), (65, 3), (33, 316), (21, 406), (12, 284)]
    (codeMat 285) (codeMat 317) (codeMat 285) false
    det285 det317 inv317
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space4322_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 130, 65, 33, 21, 12]) := by
  have h := frozenWangTable.lower_le_L0 55 space4322_orbit
  simpa only [lower55] using h

theorem space4323_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [263, 134, 65, 37, 21, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(263, 316), (134, 287), (65, 3), (37, 133), (21, 168), (9, 2)]
    (codeMat 286) (codeMat 405) (codeMat 407) true
    det286 det405 inv405
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space4323_lower : 14 ≤ frozenWangTable.L0 (spanCodes [263, 134, 65, 37, 21, 9]) := by
  have h := frozenWangTable.lower_le_L0 55 space4323_orbit
  simpa only [lower55] using h

theorem space4324_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 197), (129, 391), (65, 1), (34, 488), (19, 440), (10, 456), (6, 128)]
    (codeMat 85) (codeMat 407) (codeMat 405) false
    det85 det407 inv407
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4324_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space4324_orbit
  simpa only [lower17] using h

theorem space4325_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 67, 35, 17, 11, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 451), (128, 1), (67, 391), (35, 408), (17, 456), (11, 440), (6, 128)]
    (codeMat 84) (codeMat 111) (codeMat 412) false
    det84 det111 inv111
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4325_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 17, 11, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space4325_orbit
  simpa only [lower17] using h

theorem space4326_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 67, 34, 17, 8, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 197), (129, 263), (67, 196), (34, 488), (17, 312), (8, 32), (6, 128)]
    (codeMat 84) (codeMat 470) (codeMat 213) false
    det84 det470 inv470
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4326_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 67, 34, 17, 8, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space4326_orbit
  simpa only [lower17] using h

theorem space4327_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [290, 163, 67, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(290, 336), (163, 431), (67, 356), (16, 325), (11, 324), (7, 192)]
    (codeMat 115) (codeMat 226) (codeMat 141) false
    det115 det226 inv226
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space4327_lower : 14 ≤ frozenWangTable.L0 (spanCodes [290, 163, 67, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 74 space4327_orbit
  simpa only [lower74] using h

theorem space4328_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 67, 34, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 63), (129, 100), (67, 329), (34, 312), (16, 32), (11, 328), (7, 128)]
    (codeMat 86) (codeMat 421) (codeMat 179) false
    det86 det421 inv421
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4328_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 67, 34, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4328_orbit
  simpa only [lower17] using h

theorem space4329_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 67, 33, 19, 11, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 322), (130, 390), (67, 323), (33, 80), (19, 240), (11, 408), (4, 128)]
    (codeMat 92) (codeMat 185) (codeMat 481) false
    det92 det185 inv185
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4329_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 33, 19, 11, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space4329_orbit
  simpa only [lower17] using h

theorem space4330_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 67, 34, 19, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 274), (129, 329), (67, 301), (34, 208), (19, 328), (8, 360), (4, 128)]
    (codeMat 95) (codeMat 99) (codeMat 172) false
    det95 det99 inv99
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4330_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 67, 34, 19, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space4330_orbit
  simpa only [lower17] using h

theorem space4331_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 129, 67, 34, 18, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 1), (129, 196), (67, 451), (34, 328), (18, 32), (11, 280), (5, 128)]
    (codeMat 92) (codeMat 141) (codeMat 226) false
    det92 det141 inv141
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4331_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 67, 34, 18, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space4331_orbit
  simpa only [lower17] using h

theorem space4332_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 133, 65, 37, 21, 12, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 391), (133, 323), (65, 1), (37, 440), (21, 408), (12, 456), (3, 128)]
    (codeMat 85) (codeMat 311) (codeMat 307) false
    det85 det311 inv311
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4332_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 37, 21, 12, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space4332_orbit
  simpa only [lower17] using h

theorem space4333_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [260, 133, 68, 37, 16, 12, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(260, 1), (133, 197), (68, 391), (37, 456), (16, 360), (12, 440), (3, 128)]
    (codeMat 93) (codeMat 207) (codeMat 370) false
    det93 det207 inv207
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4333_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 37, 16, 12, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space4333_orbit
  simpa only [lower17] using h

theorem space4334_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 64, 34, 19, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 263), (129, 323), (64, 390), (34, 312), (19, 408), (11, 240), (7, 128)]
    (codeMat 93) (codeMat 382) (codeMat 499) false
    det93 det382 inv382
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4334_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 34, 19, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4334_orbit
  simpa only [lower17] using h

theorem space4335_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 65, 32, 18, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 228), (131, 429), (65, 219), (32, 32), (18, 360), (11, 408), (7, 128)]
    (codeMat 86) (codeMat 395) (codeMat 474) false
    det86 det395 inv395
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4335_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 18, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4335_orbit
  simpa only [lower17] using h

theorem space4336_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 67, 34, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 502), (129, 301), (67, 329), (34, 240), (16, 360), (11, 328), (7, 128)]
    (codeMat 94) (codeMat 419) (codeMat 183) false
    det94 det419 inv419
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4336_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 34, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4336_orbit
  simpa only [lower17] using h

theorem space4337_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 67, 34, 16, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 91), (129, 301), (67, 100), (34, 408), (16, 360), (9, 32), (7, 128)]
    (codeMat 95) (codeMat 230) (codeMat 159) false
    det95 det230 inv230
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4337_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 67, 34, 16, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space4337_orbit
  simpa only [lower17] using h

theorem space4338_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 67, 34, 19, 11, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 450), (129, 451), (67, 263), (34, 208), (19, 280), (11, 312), (4, 128)]
    (codeMat 84) (codeMat 123) (codeMat 236) false
    det84 det123 inv123
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4338_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 34, 19, 11, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space4338_orbit
  simpa only [lower17] using h

theorem space4339_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 134, 66, 36, 22, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 196), (134, 263), (66, 322), (36, 32), (22, 312), (14, 80), (1, 128)]
    (codeMat 93) (codeMat 410) (codeMat 331) false
    det93 det410 inv410
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4339_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 134, 66, 36, 22, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space4339_orbit
  simpa only [lower17] using h

theorem space4340_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [262, 132, 70, 38, 18, 12, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(262, 451), (132, 196), (70, 450), (38, 280), (18, 32), (12, 80), (1, 128)]
    (codeMat 92) (codeMat 172) (codeMat 99) false
    det92 det172 inv172
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space4340_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 132, 70, 38, 18, 12, 1]) := by
  have h := frozenWangTable.lower_le_L0 17 space4340_orbit
  simpa only [lower17] using h

theorem space4341_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [128, 68, 32, 16, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(128, 256), (68, 336), (32, 2), (16, 4), (8, 5), (3, 8)]
    (codeMat 266) (codeMat 225) (codeMat 169) false
    det266 det225 inv225
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4341_lower : 12 ≤ frozenWangTable.L0 (spanCodes [128, 68, 32, 16, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 25 space4341_orbit
  simpa only [lower25] using h

theorem space4342_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [132, 68, 36, 16, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(132, 70), (68, 198), (36, 54), (16, 8), (12, 30), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 299) (codeMat 318) false
    det273 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4342_lower : 12 ≤ frozenWangTable.L0 (spanCodes [132, 68, 36, 16, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4342_orbit
  simpa only [lower11] using h

theorem space4343_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [131, 64, 32, 19, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(131, 139), (64, 9), (32, 32), (19, 136), (8, 8), (7, 432)]
    (codeMat 214) (codeMat 275) (codeMat 275) false
    det214 det275 inv275
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space4343_lower : 12 ≤ frozenWangTable.L0 (spanCodes [131, 64, 32, 19, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 43 space4343_orbit
  simpa only [lower43] using h

theorem space4344_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [128, 66, 34, 18, 8, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(128, 128), (66, 80), (34, 52), (18, 2), (8, 9), (4, 32), (1, 8)]
    (codeMat 267) (codeMat 273) (codeMat 273) false
    det267 det273 inv273
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4344_lower : 12 ≤ frozenWangTable.L0 (spanCodes [128, 66, 34, 18, 8, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4344_orbit
  simpa only [lower11] using h

theorem space4345_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [128, 66, 34, 16, 8, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(128, 128), (66, 80), (34, 22), (16, 2), (8, 1), (6, 32), (1, 8)]
    (codeMat 266) (codeMat 305) (codeMat 305) false
    det266 det305 inv305
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4345_lower : 12 ≤ frozenWangTable.L0 (spanCodes [128, 66, 34, 16, 8, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4345_orbit
  simpa only [lower11] using h

theorem space4346_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [129, 65, 32, 16, 9, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(129, 88), (65, 216), (32, 54), (16, 9), (9, 3), (5, 40), (2, 8)]
    (codeMat 267) (codeMat 299) (codeMat 318) false
    det267 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4346_lower : 12 ≤ frozenWangTable.L0 (spanCodes [129, 65, 32, 16, 9, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4346_orbit
  simpa only [lower11] using h

theorem space4347_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [129, 64, 33, 16, 8, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(129, 208), (64, 128), (33, 20), (16, 3), (8, 2), (4, 32), (3, 8)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    det266 det282 inv282
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4347_lower : 12 ≤ frozenWangTable.L0 (spanCodes [129, 64, 33, 16, 8, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4347_orbit
  simpa only [lower11] using h

theorem space4348_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [132, 68, 36, 16, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(132, 336), (68, 338), (36, 256), (16, 8), (8, 9), (3, 5)]
    (codeMat 226) (codeMat 281) (codeMat 281) true
    det226 det281 inv281
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space4348_lower : 12 ≤ frozenWangTable.L0 (spanCodes [132, 68, 36, 16, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 25 space4348_orbit
  simpa only [lower25] using h

theorem space4349_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [132, 64, 36, 20, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(132, 198), (64, 128), (36, 54), (20, 30), (12, 22), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 314) (codeMat 271) false
    det273 det314 inv314
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4349_lower : 12 ≤ frozenWangTable.L0 (spanCodes [132, 64, 36, 20, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space4349_orbit
  simpa only [lower11] using h

theorem space4350_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 145, 81, 49, 8, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 485), (145, 487), (81, 484), (49, 160), (8, 256), (5, 8), (3, 24)]
    (codeMat 140) (codeMat 470) (codeMat 213) false
    det140 det470 inv470
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4350_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 49, 8, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4350_orbit
  simpa only [lower10] using h

theorem space4351_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 144, 81, 48, 8, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 382), (144, 360), (81, 374), (48, 128), (8, 384), (5, 1), (3, 3)]
    (codeMat 161) (codeMat 494) (codeMat 501) false
    det161 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4351_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 144, 81, 48, 8, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4351_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
