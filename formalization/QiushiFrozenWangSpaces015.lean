import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0480_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [256, 134, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(256, 256), (134, 272), (103, 396), (19, 238), (10, 371)]
    (codeMat 302) (codeMat 409) (codeMat 473) false
    det302 det409 inv409
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0480_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0480_orbit
  simpa only [lower231] using h

theorem space0481_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 131, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (131, 440), (102, 492), (19, 441), (10, 462)]
    (codeMat 302) (codeMat 330) (codeMat 394) false
    det302 det330 inv330
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0481_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0481_orbit
  simpa only [lower144] using h

theorem space0482_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 164, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (164, 411), (65, 1), (19, 119), (10, 462)]
    (codeMat 309) (codeMat 181) (codeMat 423) false
    det309 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0482_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 164, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0482_orbit
  simpa only [lower144] using h

theorem space0483_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 161, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (161, 84), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 179) (codeMat 421) false
    det372 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0483_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 161, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0483_orbit
  simpa only [lower144] using h

theorem space0484_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 134, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (134, 493), (67, 118), (19, 462), (10, 119)]
    (codeMat 311) (codeMat 179) (codeMat 421) false
    det311 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0484_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 134, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0484_orbit
  simpa only [lower144] using h

theorem space0485_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 161, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 408), (161, 85), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 405) (codeMat 407) false
    det358 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0485_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 161, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0485_orbit
  simpa only [lower144] using h

theorem space0486_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 163, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (163, 492), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 401) (codeMat 401) false
    det358 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0486_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0486_orbit
  simpa only [lower144] using h

theorem space0487_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [263, 164, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(263, 408), (164, 493), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 407) (codeMat 405) false
    det302 det407 inv407
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0487_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 164, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0487_orbit
  simpa only [lower144] using h

theorem space0488_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 167, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (167, 84), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 403) (codeMat 403) false
    det302 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0488_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 167, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0488_orbit
  simpa only [lower144] using h

theorem space0489_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 135, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (135, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 401) (codeMat 401) false
    det318 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0489_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 135, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0489_orbit
  simpa only [lower144] using h

theorem space0490_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [293, 134, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(293, 33), (134, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 405) (codeMat 407) false
    det318 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0490_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 134, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0490_orbit
  simpa only [lower144] using h

theorem space0491_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [260, 161, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(260, 16), (161, 114), (68, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 234) (codeMat 461) false
    det302 det234 inv234
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0491_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0491_orbit
  simpa only [lower231] using h

theorem space0492_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 129, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (129, 118), (68, 411), (19, 119), (10, 441)]
    (codeMat 311) (codeMat 110) (codeMat 444) false
    det311 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0492_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 129, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0492_orbit
  simpa only [lower144] using h

theorem space0493_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [294, 131, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(294, 33), (131, 118), (68, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 335) (codeMat 426) false
    det318 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0493_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 131, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0493_orbit
  simpa only [lower144] using h

theorem space0494_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 133, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (133, 493), (68, 411), (19, 462), (10, 441)]
    (codeMat 318) (codeMat 254) (codeMat 443) false
    det318 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0494_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0494_orbit
  simpa only [lower144] using h

theorem space0495_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [291, 134, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(291, 33), (134, 411), (68, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 477) (codeMat 431) false
    det311 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0495_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 134, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0495_orbit
  simpa only [lower144] using h

theorem space0496_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 134, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (134, 493), (71, 411), (19, 462), (10, 441)]
    (codeMat 318) (codeMat 250) (codeMat 397) false
    det318 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0496_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 134, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0496_orbit
  simpa only [lower144] using h

theorem space0497_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 131, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (131, 118), (70, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 331) (codeMat 410) false
    det318 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0497_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 131, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0497_orbit
  simpa only [lower144] using h

theorem space0498_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [261, 197, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(261, 495), (197, 493), (33, 463), (19, 119), (10, 441)]
    (codeMat 482) (codeMat 241) (codeMat 489) true
    det482 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0498_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 197, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0498_orbit
  simpa only [lower144] using h

theorem space0499_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (196, 34), (33, 440), (19, 119), (10, 462)]
    (codeMat 354) (codeMat 234) (codeMat 461) true
    det354 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0499_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0499_orbit
  simpa only [lower144] using h

theorem space0500_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 133, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 32), (133, 34), (33, 463), (19, 441), (10, 119)]
    (codeMat 354) (codeMat 375) (codeMat 491) true
    det354 det375 inv375
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0500_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 133, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0500_orbit
  simpa only [lower144] using h

theorem space0501_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [326, 134, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(326, 495), (134, 493), (33, 440), (19, 462), (10, 119)]
    (codeMat 482) (codeMat 346) (codeMat 459) true
    det482 det346 inv346
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0501_lower : 15 ≤ frozenWangTable.L0 (spanCodes [326, 134, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0501_orbit
  simpa only [lower144] using h

theorem space0502_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [388, 68, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(388, 495), (68, 493), (33, 118), (19, 441), (10, 462)]
    (codeMat 482) (codeMat 431) (codeMat 477) true
    det482 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0502_lower : 15 ≤ frozenWangTable.L0 (spanCodes [388, 68, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0502_orbit
  simpa only [lower144] using h

theorem space0503_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [390, 70, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(390, 32), (70, 34), (33, 118), (19, 462), (10, 441)]
    (codeMat 354) (codeMat 409) (codeMat 473) true
    det354 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0503_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 70, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0503_orbit
  simpa only [lower144] using h

theorem space0504_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 197, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (197, 493), (32, 1), (19, 119), (10, 441)]
    (codeMat 426) (codeMat 213) (codeMat 470) true
    det426 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0504_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 197, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0504_orbit
  simpa only [lower144] using h

theorem space0505_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 129, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (129, 414), (32, 36), (19, 350), (10, 245)]
    (codeMat 486) (codeMat 346) (codeMat 459) false
    det486 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0505_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 129, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0505_orbit
  simpa only [lower220] using h

theorem space0506_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 65, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (65, 192), (32, 36), (19, 350), (10, 427)]
    (codeMat 358) (codeMat 409) (codeMat 473) false
    det358 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0506_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 65, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0506_orbit
  simpa only [lower220] using h

theorem space0507_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 469), (132, 378), (67, 462), (32, 16), (19, 446), (10, 463)]
    (codeMat 407) (codeMat 179) (codeMat 421) false
    det407 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0507_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0507_orbit
  simpa only [lower69] using h

theorem space0508_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 130, 68, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 436), (130, 1), (68, 362), (32, 16), (19, 446), (10, 113)]
    (codeMat 405) (codeMat 107) (codeMat 428) false
    det405 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0508_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 130, 68, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0508_orbit
  simpa only [lower69] using h

theorem space0509_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 135, 71, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 453), (135, 197), (71, 196), (32, 16), (19, 113), (10, 446)]
    (codeMat 340) (codeMat 249) (codeMat 425) false
    det340 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0509_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 71, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0509_orbit
  simpa only [lower69] using h

theorem space0510_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 134, 70, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 436), (134, 362), (70, 363), (32, 16), (19, 113), (10, 463)]
    (codeMat 468) (codeMat 250) (codeMat 397) false
    det468 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0510_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 70, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0510_orbit
  simpa only [lower69] using h

theorem space0511_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 194, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (194, 414), (35, 209), (19, 245), (10, 427)]
    (codeMat 486) (codeMat 241) (codeMat 489) false
    det486 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0511_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 194, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0511_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
