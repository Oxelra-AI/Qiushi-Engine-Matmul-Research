import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0512_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 130, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (130, 192), (35, 399), (19, 427), (10, 245)]
    (codeMat 358) (codeMat 375) (codeMat 491) false
    det358 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0512_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 130, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0512_orbit
  simpa only [lower220] using h

theorem space0513_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 133, 64, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 223), (133, 363), (64, 1), (35, 479), (19, 463), (10, 446)]
    (codeMat 468) (codeMat 401) (codeMat 401) false
    det468 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0513_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 64, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0513_orbit
  simpa only [lower69] using h

theorem space0514_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 135, 64, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 257), (135, 196), (64, 1), (35, 430), (19, 446), (10, 463)]
    (codeMat 340) (codeMat 407) (codeMat 405) false
    det340 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0514_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 64, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0514_orbit
  simpa only [lower69] using h

theorem space0515_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 134, 69, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 222), (134, 362), (69, 363), (35, 97), (19, 113), (10, 463)]
    (codeMat 405) (codeMat 478) (codeMat 445) false
    det405 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0515_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 134, 69, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0515_orbit
  simpa only [lower69] using h

theorem space0516_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [390, 68, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(390, 2), (68, 493), (35, 440), (19, 441), (10, 462)]
    (codeMat 426) (codeMat 395) (codeMat 474) true
    det426 det395 inv395
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0516_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 68, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0516_orbit
  simpa only [lower144] using h

theorem space0517_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 129, 71, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (129, 462), (71, 180), (35, 479), (19, 463), (10, 113)]
    (codeMat 407) (codeMat 110) (codeMat 444) false
    det407 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0517_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 71, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0517_orbit
  simpa only [lower69] using h

theorem space0518_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 134, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (134, 493), (34, 118), (19, 462), (10, 119)]
    (codeMat 426) (codeMat 382) (codeMat 499) true
    det426 det382 inv382
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0518_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 134, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0518_orbit
  simpa only [lower144] using h

theorem space0519_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 65, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 437), (132, 363), (65, 1), (34, 430), (19, 463), (10, 446)]
    (codeMat 405) (codeMat 181) (codeMat 423) false
    det405 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0519_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 65, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0519_orbit
  simpa only [lower69] using h

theorem space0520_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 67, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (67, 414), (34, 378), (19, 427), (10, 350)]
    (codeMat 486) (codeMat 431) (codeMat 477) false
    det486 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0520_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 67, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0520_orbit
  simpa only [lower220] using h

theorem space0521_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 128, 68, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 222), (128, 1), (68, 362), (34, 97), (19, 446), (10, 113)]
    (codeMat 468) (codeMat 335) (codeMat 426) false
    det468 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0521_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 128, 68, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0521_orbit
  simpa only [lower69] using h

theorem space0522_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 128, 71, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (128, 1), (71, 197), (34, 97), (19, 463), (10, 113)]
    (codeMat 340) (codeMat 330) (codeMat 394) false
    det340 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0522_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 71, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0522_orbit
  simpa only [lower69] using h

theorem space0523_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 192, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (192, 192), (37, 378), (19, 350), (10, 245)]
    (codeMat 302) (codeMat 241) (codeMat 489) false
    det302 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0523_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 192, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0523_orbit
  simpa only [lower220] using h

theorem space0524_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 129, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (129, 414), (37, 378), (19, 350), (10, 427)]
    (codeMat 494) (codeMat 375) (codeMat 491) false
    det494 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0524_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 129, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0524_orbit
  simpa only [lower220] using h

theorem space0525_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 133, 65, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (133, 197), (65, 1), (37, 97), (19, 113), (10, 463)]
    (codeMat 285) (codeMat 401) (codeMat 401) false
    det285 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0525_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0525_orbit
  simpa only [lower69] using h

theorem space0526_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 134, 65, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 222), (134, 362), (65, 1), (37, 97), (19, 113), (10, 446)]
    (codeMat 477) (codeMat 407) (codeMat 405) false
    det477 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0526_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 134, 65, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0526_orbit
  simpa only [lower69] using h

theorem space0527_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 128, 69, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 437), (128, 1), (69, 363), (37, 430), (19, 446), (10, 463)]
    (codeMat 412) (codeMat 110) (codeMat 444) false
    det412 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0527_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 69, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0527_orbit
  simpa only [lower69] using h

theorem space0528_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 68, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 2), (68, 493), (37, 118), (19, 119), (10, 462)]
    (codeMat 419) (codeMat 445) (codeMat 478) true
    det419 det445 inv445
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0528_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 68, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0528_orbit
  simpa only [lower144] using h

theorem space0529_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 70, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 175), (132, 378), (70, 180), (37, 430), (19, 446), (10, 113)]
    (codeMat 415) (codeMat 478) (codeMat 445) false
    det415 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0529_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 70, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0529_orbit
  simpa only [lower69] using h

theorem space0530_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 197, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (197, 493), (36, 1), (19, 441), (10, 119)]
    (codeMat 419) (codeMat 206) (codeMat 498) true
    det419 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0530_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 197, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0530_orbit
  simpa only [lower144] using h

theorem space0531_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 128, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (128, 192), (36, 36), (19, 427), (10, 350)]
    (codeMat 302) (codeMat 346) (codeMat 459) false
    det302 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0531_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 128, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0531_orbit
  simpa only [lower220] using h

theorem space0532_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 134, 64, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 436), (134, 362), (64, 1), (36, 16), (19, 113), (10, 446)]
    (codeMat 412) (codeMat 179) (codeMat 421) false
    det412 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0532_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 134, 64, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0532_orbit
  simpa only [lower69] using h

theorem space0533_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [390, 67, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(390, 16), (67, 414), (36, 36), (19, 245), (10, 350)]
    (codeMat 494) (codeMat 409) (codeMat 473) false
    det494 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0533_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 67, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0533_orbit
  simpa only [lower220] using h

theorem space0534_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 129, 69, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 469), (129, 462), (69, 378), (36, 16), (19, 463), (10, 446)]
    (codeMat 415) (codeMat 107) (codeMat 428) false
    det415 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0534_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 69, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0534_orbit
  simpa only [lower69] using h

theorem space0535_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 135, 68, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 436), (135, 363), (68, 362), (36, 16), (19, 463), (10, 113)]
    (codeMat 477) (codeMat 249) (codeMat 425) false
    det477 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0535_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 68, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0535_orbit
  simpa only [lower69] using h

theorem space0536_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 133, 70, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 453), (133, 196), (70, 197), (36, 16), (19, 446), (10, 113)]
    (codeMat 285) (codeMat 250) (codeMat 397) false
    det285 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0536_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 70, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0536_orbit
  simpa only [lower69] using h

theorem space0537_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 194, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (194, 414), (39, 209), (19, 427), (10, 245)]
    (codeMat 494) (codeMat 234) (codeMat 461) false
    det494 det234 inv234
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0537_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 194, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0537_orbit
  simpa only [lower220] using h

theorem space0538_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 134, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (134, 493), (39, 440), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 339) (codeMat 467) true
    det419 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0538_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 134, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0538_orbit
  simpa only [lower144] using h

theorem space0539_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [390, 64, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(390, 16), (64, 192), (39, 399), (19, 245), (10, 427)]
    (codeMat 302) (codeMat 431) (codeMat 477) false
    det302 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0539_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 64, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0539_orbit
  simpa only [lower220] using h

theorem space0540_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 133, 67, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (133, 180), (67, 462), (39, 479), (19, 113), (10, 463)]
    (codeMat 415) (codeMat 181) (codeMat 423) false
    det415 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0540_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 67, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0540_orbit
  simpa only [lower69] using h

theorem space0541_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 68, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 222), (132, 363), (68, 362), (39, 97), (19, 463), (10, 113)]
    (codeMat 412) (codeMat 477) (codeMat 431) false
    det412 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0541_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 68, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0541_orbit
  simpa only [lower69] using h

theorem space0542_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 130, 71, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 223), (130, 1), (71, 363), (39, 479), (19, 446), (10, 463)]
    (codeMat 477) (codeMat 330) (codeMat 394) false
    det477 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0542_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 71, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0542_orbit
  simpa only [lower69] using h

theorem space0543_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 130, 70, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 257), (130, 1), (70, 196), (39, 430), (19, 463), (10, 446)]
    (codeMat 285) (codeMat 335) (codeMat 426) false
    det285 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0543_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 70, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0543_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
