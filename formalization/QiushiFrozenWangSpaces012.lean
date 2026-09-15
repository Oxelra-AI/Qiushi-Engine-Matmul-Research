import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0384_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 162, 96, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 272), (162, 196), (96, 180), (19, 463), (10, 446), (5, 16)]
    (codeMat 335) (codeMat 474) (codeMat 395) false
    det335 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0384_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 96, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0384_orbit
  simpa only [lower69] using h

theorem space0385_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [261, 128, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(261, 68), (128, 40), (65, 1), (17, 20), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    det85 det273 inv273
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0385_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0385_orbit
  simpa only [lower31] using h

theorem space0386_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [261, 129, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(261, 100), (129, 33), (65, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 85) (codeMat 267) (codeMat 282) true
    det85 det267 inv267
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0386_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0386_orbit
  simpa only [lower31] using h

theorem space0387_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (132, 34), (71, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 249) (codeMat 425) false
    det421 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0387_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0387_orbit
  simpa only [lower144] using h

theorem space0388_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 130, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 33), (130, 1), (71, 34), (19, 119), (10, 441)]
    (codeMat 421) (codeMat 334) (codeMat 442) false
    det421 det334 inv334
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0388_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0388_orbit
  simpa only [lower144] using h

theorem space0389_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (128, 1), (71, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 107) (codeMat 428) false
    det428 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0389_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0389_orbit
  simpa only [lower144] using h

theorem space0390_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [288, 160, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(288, 1), (160, 257), (71, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 206) (codeMat 498) false
    det302 det206 inv206
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0390_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0390_orbit
  simpa only [lower231] using h

theorem space0391_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 135, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (135, 34), (68, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 253) (codeMat 415) false
    det421 det253 inv253
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0391_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0391_orbit
  simpa only [lower144] using h

theorem space0392_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 160, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (160, 411), (67, 440), (19, 462), (10, 441)]
    (codeMat 303) (codeMat 181) (codeMat 423) false
    det303 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0392_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 160, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0392_orbit
  simpa only [lower144] using h

theorem space0393_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 165, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (165, 410), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 179) (codeMat 421) false
    det302 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0393_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 165, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0393_orbit
  simpa only [lower144] using h

theorem space0394_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 135, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 33), (135, 35), (65, 1), (19, 462), (10, 119)]
    (codeMat 421) (codeMat 407) (codeMat 405) false
    det421 det407 inv407
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0394_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0394_orbit
  simpa only [lower144] using h

theorem space0395_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (134, 35), (65, 1), (19, 462), (10, 119)]
    (codeMat 421) (codeMat 403) (codeMat 403) false
    det421 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0395_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0395_orbit
  simpa only [lower144] using h

theorem space0396_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 166, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (166, 34), (65, 1), (19, 119), (10, 462)]
    (codeMat 309) (codeMat 401) (codeMat 401) false
    det309 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0396_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0396_orbit
  simpa only [lower144] using h

theorem space0397_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [291, 165, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(291, 495), (165, 492), (65, 1), (19, 119), (10, 462)]
    (codeMat 309) (codeMat 405) (codeMat 407) false
    det309 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0397_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 165, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0397_orbit
  simpa only [lower144] using h

theorem space0398_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 162, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (162, 35), (65, 1), (19, 441), (10, 462)]
    (codeMat 317) (codeMat 403) (codeMat 403) false
    det317 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0398_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0398_orbit
  simpa only [lower144] using h

theorem space0399_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [294, 160, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(294, 495), (160, 493), (65, 1), (19, 441), (10, 462)]
    (codeMat 317) (codeMat 407) (codeMat 405) false
    det317 det407 inv407
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0399_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 160, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0399_orbit
  simpa only [lower144] using h

theorem space0400_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 135, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (135, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 181) (codeMat 423) false
    det428 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0400_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0400_orbit
  simpa only [lower144] using h

theorem space0401_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 165, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (165, 84), (102, 85), (19, 441), (10, 119)]
    (codeMat 309) (codeMat 250) (codeMat 397) false
    det309 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0401_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 165, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0401_orbit
  simpa only [lower144] using h

theorem space0402_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 130, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (130, 1), (101, 35), (19, 462), (10, 441)]
    (codeMat 309) (codeMat 331) (codeMat 410) false
    det309 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0402_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 130, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0402_orbit
  simpa only [lower144] using h

theorem space0403_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [292, 135, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(292, 511), (135, 272), (100, 255), (19, 238), (10, 371)]
    (codeMat 302) (codeMat 445) (codeMat 478) false
    det302 det445 inv445
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0403_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 135, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0403_orbit
  simpa only [lower231] using h

theorem space0404_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (131, 440), (100, 411), (19, 441), (10, 462)]
    (codeMat 302) (codeMat 110) (codeMat 444) false
    det302 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0404_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0404_orbit
  simpa only [lower144] using h

theorem space0405_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [289, 130, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(289, 495), (130, 1), (100, 493), (19, 462), (10, 441)]
    (codeMat 309) (codeMat 335) (codeMat 426) false
    det309 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0405_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 130, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0405_orbit
  simpa only [lower144] using h

theorem space0406_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 167, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (167, 410), (100, 411), (19, 441), (10, 119)]
    (codeMat 309) (codeMat 254) (codeMat 443) false
    det309 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0406_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 167, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0406_orbit
  simpa only [lower144] using h

theorem space0407_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [262, 165, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(262, 408), (165, 85), (100, 493), (19, 462), (10, 119)]
    (codeMat 302) (codeMat 477) (codeMat 431) false
    det302 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0407_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 165, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0407_orbit
  simpa only [lower144] using h

theorem space0408_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 160, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (160, 411), (99, 410), (19, 119), (10, 441)]
    (codeMat 317) (codeMat 253) (codeMat 415) false
    det317 det253 inv253
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0408_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 160, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0408_orbit
  simpa only [lower144] using h

theorem space0409_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 129, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (129, 440), (98, 410), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 107) (codeMat 428) false
    det303 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0409_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 129, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0409_orbit
  simpa only [lower144] using h

theorem space0410_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [256, 165, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(256, 256), (165, 396), (98, 156), (19, 371), (10, 413)]
    (codeMat 302) (codeMat 339) (codeMat 467) false
    det302 det339 inv339
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0410_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 165, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0410_orbit
  simpa only [lower231] using h

theorem space0411_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 161, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (161, 85), (98, 84), (19, 119), (10, 441)]
    (codeMat 317) (codeMat 249) (codeMat 425) false
    det317 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0411_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0411_orbit
  simpa only [lower144] using h

theorem space0412_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 224, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (224, 34), (19, 441), (10, 462), (7, 1)]
    (codeMat 417) (codeMat 241) (codeMat 489) true
    det417 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0412_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 224, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0412_orbit
  simpa only [lower144] using h

theorem space0413_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 162, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 409), (162, 411), (19, 119), (10, 441), (7, 1)]
    (codeMat 417) (codeMat 346) (codeMat 459) true
    det417 det346 inv346
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0413_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 162, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0413_orbit
  simpa only [lower144] using h

theorem space0414_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [352, 160, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(352, 495), (160, 493), (19, 119), (10, 462), (7, 1)]
    (codeMat 481) (codeMat 375) (codeMat 491) true
    det481 det375 inv375
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0414_lower : 15 ≤ frozenWangTable.L0 (spanCodes [352, 160, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0414_orbit
  simpa only [lower144] using h

theorem space0415_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [419, 99, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(419, 494), (99, 492), (19, 462), (10, 119), (7, 1)]
    (codeMat 417) (codeMat 431) (codeMat 477) true
    det417 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0415_lower : 15 ≤ frozenWangTable.L0 (spanCodes [419, 99, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0415_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
