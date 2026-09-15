import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0736_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 163, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (163, 84), (65, 1), (19, 441), (10, 462)]
    (codeMat 317) (codeMat 179) (codeMat 421) false
    det317 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0736_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 163, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0736_orbit
  simpa only [lower144] using h

theorem space0737_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [262, 198, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(262, 495), (198, 493), (38, 463), (19, 441), (10, 119)]
    (codeMat 419) (codeMat 234) (codeMat 461) true
    det419 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0737_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 198, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0737_orbit
  simpa only [lower144] using h

theorem space0738_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (196, 34), (38, 440), (19, 462), (10, 119)]
    (codeMat 355) (codeMat 241) (codeMat 489) true
    det355 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0738_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0738_orbit
  simpa only [lower144] using h

theorem space0739_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [324, 132, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(324, 495), (132, 493), (38, 118), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 375) (codeMat 491) true
    det419 det375 inv375
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0739_lower : 15 ≤ frozenWangTable.L0 (spanCodes [324, 132, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0739_orbit
  simpa only [lower144] using h

theorem space0740_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 133, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 32), (133, 34), (38, 118), (19, 441), (10, 462)]
    (codeMat 355) (codeMat 346) (codeMat 459) true
    det355 det346 inv346
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0740_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 133, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0740_orbit
  simpa only [lower144] using h

theorem space0741_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [390, 70, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(390, 32), (70, 34), (38, 463), (19, 119), (10, 441)]
    (codeMat 355) (codeMat 431) (codeMat 477) true
    det355 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0741_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 70, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0741_orbit
  simpa only [lower144] using h

theorem space0742_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [389, 69, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(389, 495), (69, 493), (38, 440), (19, 119), (10, 462)]
    (codeMat 419) (codeMat 409) (codeMat 473) true
    det419 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0742_lower : 15 ≤ frozenWangTable.L0 (spanCodes [389, 69, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0742_orbit
  simpa only [lower144] using h

theorem space0743_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 193, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (193, 414), (39, 209), (19, 427), (10, 245)]
    (codeMat 423) (codeMat 234) (codeMat 461) false
    det423 det234 inv234
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0743_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 193, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0743_orbit
  simpa only [lower220] using h

theorem space0744_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 132, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (132, 493), (39, 440), (19, 462), (10, 441)]
    (codeMat 491) (codeMat 339) (codeMat 467) true
    det491 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0744_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 132, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0744_orbit
  simpa only [lower144] using h

theorem space0745_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 128, 70, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 223), (128, 1), (70, 363), (39, 479), (19, 446), (10, 463)]
    (codeMat 412) (codeMat 330) (codeMat 394) false
    det412 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0745_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 128, 70, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0745_orbit
  simpa only [lower69] using h

theorem space0746_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 128, 71, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 257), (128, 1), (71, 196), (39, 430), (19, 463), (10, 446)]
    (codeMat 348) (codeMat 335) (codeMat 426) false
    det348 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0746_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 71, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0746_orbit
  simpa only [lower69] using h

theorem space0747_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 69, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 222), (134, 363), (69, 362), (39, 97), (19, 463), (10, 113)]
    (codeMat 477) (codeMat 477) (codeMat 431) false
    det477 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0747_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 69, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0747_orbit
  simpa only [lower69] using h

theorem space0748_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 135, 66, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (135, 180), (66, 462), (39, 479), (19, 113), (10, 463)]
    (codeMat 478) (codeMat 181) (codeMat 423) false
    det478 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0748_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 66, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0748_orbit
  simpa only [lower69] using h

theorem space0749_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 65, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (65, 192), (39, 399), (19, 245), (10, 427)]
    (codeMat 359) (codeMat 431) (codeMat 477) false
    det359 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0749_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 65, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0749_orbit
  simpa only [lower220] using h

theorem space0750_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 198, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (198, 493), (36, 1), (19, 441), (10, 119)]
    (codeMat 491) (codeMat 206) (codeMat 498) true
    det491 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0750_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 198, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0750_orbit
  simpa only [lower144] using h

theorem space0751_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 130, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (130, 192), (36, 36), (19, 427), (10, 350)]
    (codeMat 359) (codeMat 346) (codeMat 459) false
    det359 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0751_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 130, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0751_orbit
  simpa only [lower220] using h

theorem space0752_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 135, 71, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 453), (135, 196), (71, 197), (36, 16), (19, 446), (10, 113)]
    (codeMat 348) (codeMat 250) (codeMat 397) false
    det348 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0752_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 71, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0752_orbit
  simpa only [lower69] using h

theorem space0753_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 131, 68, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 469), (131, 462), (68, 378), (36, 16), (19, 463), (10, 446)]
    (codeMat 478) (codeMat 107) (codeMat 428) false
    det478 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0753_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 68, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0753_orbit
  simpa only [lower69] using h

theorem space0754_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 133, 69, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 436), (133, 363), (69, 362), (36, 16), (19, 463), (10, 113)]
    (codeMat 412) (codeMat 249) (codeMat 425) false
    det412 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0754_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 69, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0754_orbit
  simpa only [lower69] using h

theorem space0755_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [384, 66, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(384, 16), (66, 414), (36, 36), (19, 245), (10, 350)]
    (codeMat 423) (codeMat 409) (codeMat 473) false
    det423 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0755_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 66, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0755_orbit
  simpa only [lower220] using h

theorem space0756_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 132, 65, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 436), (132, 362), (65, 1), (36, 16), (19, 113), (10, 446)]
    (codeMat 477) (codeMat 179) (codeMat 421) false
    det477 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0756_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 132, 65, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0756_orbit
  simpa only [lower69] using h

theorem space0757_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 195, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (195, 192), (37, 378), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 241) (codeMat 489) false
    det359 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0757_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 195, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0757_orbit
  simpa only [lower220] using h

theorem space0758_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 131, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (131, 414), (37, 378), (19, 350), (10, 427)]
    (codeMat 423) (codeMat 375) (codeMat 491) false
    det423 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0758_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 131, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0758_orbit
  simpa only [lower220] using h

theorem space0759_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 71, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 175), (134, 378), (71, 180), (37, 430), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 478) (codeMat 445) false
    det478 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0759_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 71, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0759_orbit
  simpa only [lower69] using h

theorem space0760_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 130, 68, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 437), (130, 1), (68, 363), (37, 430), (19, 446), (10, 463)]
    (codeMat 477) (codeMat 110) (codeMat 444) false
    det477 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0760_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 130, 68, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0760_orbit
  simpa only [lower69] using h

theorem space0761_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [390, 69, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(390, 2), (69, 493), (37, 118), (19, 119), (10, 462)]
    (codeMat 491) (codeMat 445) (codeMat 478) true
    det491 det445 inv445
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0761_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 69, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0761_orbit
  simpa only [lower144] using h

theorem space0762_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 135, 64, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (135, 197), (64, 1), (37, 97), (19, 113), (10, 463)]
    (codeMat 348) (codeMat 401) (codeMat 401) false
    det348 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0762_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 64, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0762_orbit
  simpa only [lower69] using h

theorem space0763_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 132, 64, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 222), (132, 362), (64, 1), (37, 97), (19, 113), (10, 446)]
    (codeMat 412) (codeMat 407) (codeMat 405) false
    det412 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0763_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 132, 64, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0763_orbit
  simpa only [lower69] using h

theorem space0764_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 192, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (192, 192), (34, 378), (19, 245), (10, 350)]
    (codeMat 303) (codeMat 234) (codeMat 461) false
    det303 det234 inv234
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0764_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 192, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0764_orbit
  simpa only [lower220] using h

theorem space0765_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 132, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (132, 493), (34, 118), (19, 462), (10, 119)]
    (codeMat 482) (codeMat 382) (codeMat 499) true
    det482 det382 inv382
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0765_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 132, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0765_orbit
  simpa only [lower144] using h

theorem space0766_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 133, 68, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 175), (133, 180), (68, 378), (34, 430), (19, 113), (10, 446)]
    (codeMat 470) (codeMat 477) (codeMat 431) false
    det470 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0766_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 68, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0766_orbit
  simpa only [lower69] using h

theorem space0767_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 130, 69, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 222), (130, 1), (69, 362), (34, 97), (19, 446), (10, 113)]
    (codeMat 405) (codeMat 335) (codeMat 426) false
    det405 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0767_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 69, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0767_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
