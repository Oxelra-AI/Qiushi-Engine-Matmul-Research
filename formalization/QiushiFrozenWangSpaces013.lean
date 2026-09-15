import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0416_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [418, 98, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(418, 408), (98, 410), (19, 441), (10, 119), (7, 1)]
    (codeMat 481) (codeMat 409) (codeMat 473) true
    det481 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0416_lower : 15 ≤ frozenWangTable.L0 (spanCodes [418, 98, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0416_orbit
  simpa only [lower144] using h

theorem space0417_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 193, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (193, 53), (19, 427), (10, 350), (6, 36)]
    (codeMat 421) (codeMat 241) (codeMat 489) false
    det421 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0417_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 193, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0417_orbit
  simpa only [lower220] using h

theorem space0418_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 129, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (129, 53), (19, 245), (10, 350), (6, 36)]
    (codeMat 485) (codeMat 375) (codeMat 491) false
    det485 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0418_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 129, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0418_orbit
  simpa only [lower220] using h

theorem space0419_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 161, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (161, 266), (64, 1), (19, 446), (10, 113), (6, 16)]
    (codeMat 396) (codeMat 401) (codeMat 401) false
    det396 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0419_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 161, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0419_orbit
  simpa only [lower69] using h

theorem space0420_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 160, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 352), (160, 362), (64, 1), (19, 463), (10, 113), (6, 16)]
    (codeMat 460) (codeMat 407) (codeMat 405) false
    det460 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0420_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 160, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0420_orbit
  simpa only [lower69] using h

theorem space0421_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 163, 97, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 352), (163, 181), (97, 197), (19, 463), (10, 446), (6, 16)]
    (codeMat 335) (codeMat 478) (codeMat 445) false
    det335 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0421_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 163, 97, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0421_orbit
  simpa only [lower69] using h

theorem space0422_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 131, 96, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 11), (131, 112), (96, 363), (19, 113), (10, 446), (6, 16)]
    (codeMat 334) (codeMat 110) (codeMat 444) false
    det334 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0422_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 131, 96, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0422_orbit
  simpa only [lower69] using h

theorem space0423_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 194, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (194, 53), (19, 350), (10, 427), (5, 36)]
    (codeMat 485) (codeMat 234) (codeMat 461) false
    det485 det234 inv234
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0423_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 194, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0423_orbit
  simpa only [lower220] using h

theorem space0424_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 160, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 460), (160, 493), (19, 119), (10, 462), (5, 1)]
    (codeMat 369) (codeMat 339) (codeMat 467) true
    det369 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0424_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 160, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0424_orbit
  simpa only [lower144] using h

theorem space0425_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 161, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (161, 379), (67, 112), (19, 446), (10, 113), (5, 16)]
    (codeMat 335) (codeMat 181) (codeMat 423) false
    det335 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0425_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 161, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0425_orbit
  simpa only [lower69] using h

theorem space0426_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 66, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (66, 53), (19, 350), (10, 245), (5, 36)]
    (codeMat 421) (codeMat 431) (codeMat 477) false
    det421 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0426_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 66, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0426_orbit
  simpa only [lower220] using h

theorem space0427_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 128, 99, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 272), (128, 1), (99, 282), (19, 113), (10, 446), (5, 16)]
    (codeMat 460) (codeMat 330) (codeMat 394) false
    det460 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0427_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 128, 99, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0427_orbit
  simpa only [lower69] using h

theorem space0428_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 163, 98, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 352), (163, 213), (98, 165), (19, 446), (10, 463), (5, 16)]
    (codeMat 334) (codeMat 477) (codeMat 431) false
    det334 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0428_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 163, 98, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0428_orbit
  simpa only [lower69] using h

theorem space0429_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 128, 97, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 368), (128, 1), (97, 378), (19, 113), (10, 463), (5, 16)]
    (codeMat 396) (codeMat 335) (codeMat 426) false
    det396 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0429_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 128, 97, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0429_orbit
  simpa only [lower69] using h

theorem space0430_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 227, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (227, 35), (19, 462), (10, 441), (4, 1)]
    (codeMat 369) (codeMat 206) (codeMat 498) true
    det369 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0430_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 227, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0430_orbit
  simpa only [lower144] using h

theorem space0431_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 131, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (131, 53), (19, 245), (10, 427), (4, 36)]
    (codeMat 421) (codeMat 346) (codeMat 459) false
    det421 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0431_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 131, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0431_orbit
  simpa only [lower220] using h

theorem space0432_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 67, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (67, 53), (19, 427), (10, 245), (4, 36)]
    (codeMat 485) (codeMat 409) (codeMat 473) false
    det485 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0432_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 67, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0432_orbit
  simpa only [lower220] using h

theorem space0433_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 160, 66, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 10), (160, 362), (66, 112), (19, 463), (10, 113), (4, 16)]
    (codeMat 334) (codeMat 179) (codeMat 421) false
    det334 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0433_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 160, 66, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0433_orbit
  simpa only [lower69] using h

theorem space0434_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 162, 98, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 10), (162, 164), (98, 165), (19, 446), (10, 463), (4, 16)]
    (codeMat 460) (codeMat 249) (codeMat 425) false
    det460 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0434_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 162, 98, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0434_orbit
  simpa only [lower69] using h

theorem space0435_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 161, 97, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 10), (161, 181), (97, 180), (19, 463), (10, 446), (4, 16)]
    (codeMat 396) (codeMat 250) (codeMat 397) false
    det396 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0435_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 161, 97, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0435_orbit
  simpa only [lower69] using h

theorem space0436_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 129, 96, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 26), (129, 112), (96, 378), (19, 113), (10, 463), (4, 16)]
    (codeMat 335) (codeMat 107) (codeMat 428) false
    det335 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0436_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 129, 96, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0436_orbit
  simpa only [lower69] using h

theorem space0437_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (160, 34), (96, 35), (19, 119), (10, 441)]
    (codeMat 372) (codeMat 473) (codeMat 409) false
    det372 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0437_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0437_orbit
  simpa only [lower144] using h

theorem space0438_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 135, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (135, 493), (67, 118), (19, 462), (10, 119)]
    (codeMat 311) (codeMat 183) (codeMat 419) false
    det311 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0438_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 135, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0438_orbit
  simpa only [lower144] using h

theorem space0439_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (196, 34), (32, 1), (19, 119), (10, 462)]
    (codeMat 298) (codeMat 206) (codeMat 498) true
    det298 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0439_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0439_orbit
  simpa only [lower144] using h

theorem space0440_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [322, 130, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(322, 208), (130, 192), (32, 36), (19, 427), (10, 245)]
    (codeMat 358) (codeMat 339) (codeMat 467) false
    det358 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0440_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 130, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0440_orbit
  simpa only [lower220] using h

theorem space0441_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 135, 65, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 453), (135, 196), (65, 1), (32, 16), (19, 446), (10, 463)]
    (codeMat 277) (codeMat 179) (codeMat 421) false
    det277 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0441_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 65, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0441_orbit
  simpa only [lower69] using h

theorem space0442_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [387, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(387, 398), (67, 414), (32, 36), (19, 427), (10, 350)]
    (codeMat 486) (codeMat 395) (codeMat 474) false
    det486 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0442_lower : 15 ≤ frozenWangTable.L0 (spanCodes [387, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0442_orbit
  simpa only [lower220] using h

theorem space0443_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 133, 68, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 420), (133, 283), (68, 164), (32, 16), (19, 113), (10, 463)]
    (codeMat 342) (codeMat 250) (codeMat 397) false
    det342 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0443_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 133, 68, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0443_orbit
  simpa only [lower69] using h

theorem space0444_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 132, 69, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 469), (132, 180), (69, 378), (32, 16), (19, 113), (10, 446)]
    (codeMat 470) (codeMat 249) (codeMat 425) false
    det470 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0444_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 132, 69, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0444_orbit
  simpa only [lower69] using h

theorem space0445_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 129, 70, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 420), (129, 447), (70, 283), (32, 16), (19, 446), (10, 113)]
    (codeMat 279) (codeMat 107) (codeMat 428) false
    det279 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0445_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 70, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0445_orbit
  simpa only [lower69] using h

theorem space0446_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 132, 68, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 452), (132, 197), (68, 196), (33, 479), (19, 113), (10, 446)]
    (codeMat 340) (codeMat 253) (codeMat 415) false
    det340 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0446_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0446_orbit
  simpa only [lower69] using h

theorem space0447_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 133, 69, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 437), (133, 362), (69, 363), (33, 430), (19, 113), (10, 463)]
    (codeMat 468) (codeMat 254) (codeMat 443) false
    det468 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0447_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 133, 69, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0447_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
