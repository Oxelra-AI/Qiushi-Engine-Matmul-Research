import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0768_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [390, 66, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(390, 16), (66, 414), (34, 378), (19, 427), (10, 350)]
    (codeMat 431) (codeMat 431) (codeMat 477) false
    det431 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0768_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 66, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0768_orbit
  simpa only [lower220] using h

theorem space0769_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 64, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 437), (134, 363), (64, 1), (34, 430), (19, 463), (10, 446)]
    (codeMat 468) (codeMat 181) (codeMat 423) false
    det468 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0769_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 64, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0769_orbit
  simpa only [lower69] using h

theorem space0770_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 193, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (193, 414), (35, 209), (19, 245), (10, 427)]
    (codeMat 431) (codeMat 241) (codeMat 489) false
    det431 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0770_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 193, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0770_orbit
  simpa only [lower220] using h

theorem space0771_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 128, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (128, 192), (35, 399), (19, 427), (10, 245)]
    (codeMat 303) (codeMat 375) (codeMat 491) false
    det303 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0771_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 128, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0771_orbit
  simpa only [lower220] using h

theorem space0772_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 131, 70, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (131, 462), (70, 180), (35, 479), (19, 463), (10, 113)]
    (codeMat 470) (codeMat 110) (codeMat 444) false
    det470 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0772_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 70, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0772_orbit
  simpa only [lower69] using h

theorem space0773_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 132, 68, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 222), (132, 362), (68, 363), (35, 97), (19, 113), (10, 463)]
    (codeMat 468) (codeMat 478) (codeMat 445) false
    det468 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0773_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 132, 68, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0773_orbit
  simpa only [lower69] using h

theorem space0774_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 69, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 2), (69, 493), (35, 440), (19, 441), (10, 462)]
    (codeMat 482) (codeMat 395) (codeMat 474) true
    det482 det395 inv395
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0774_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 69, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0774_orbit
  simpa only [lower144] using h

theorem space0775_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 135, 65, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 223), (135, 363), (65, 1), (35, 479), (19, 463), (10, 446)]
    (codeMat 405) (codeMat 401) (codeMat 401) false
    det405 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0775_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 65, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0775_orbit
  simpa only [lower69] using h

theorem space0776_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 133, 65, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 257), (133, 196), (65, 1), (35, 430), (19, 446), (10, 463)]
    (codeMat 277) (codeMat 407) (codeMat 405) false
    det277 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0776_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0776_orbit
  simpa only [lower69] using h

theorem space0777_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 198, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (198, 493), (32, 1), (19, 119), (10, 441)]
    (codeMat 482) (codeMat 213) (codeMat 470) true
    det482 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0777_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 198, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0777_orbit
  simpa only [lower144] using h

theorem space0778_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 131, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (131, 414), (32, 36), (19, 350), (10, 245)]
    (codeMat 431) (codeMat 346) (codeMat 459) false
    det431 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0778_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 131, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0778_orbit
  simpa only [lower220] using h

theorem space0779_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 133, 70, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 453), (133, 197), (70, 196), (32, 16), (19, 113), (10, 446)]
    (codeMat 277) (codeMat 249) (codeMat 425) false
    det277 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0779_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 70, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0779_orbit
  simpa only [lower69] using h

theorem space0780_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 132, 71, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 436), (132, 362), (71, 363), (32, 16), (19, 113), (10, 463)]
    (codeMat 405) (codeMat 250) (codeMat 397) false
    det405 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0780_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 132, 71, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0780_orbit
  simpa only [lower69] using h

theorem space0781_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 128, 69, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 436), (128, 1), (69, 362), (32, 16), (19, 446), (10, 113)]
    (codeMat 468) (codeMat 107) (codeMat 428) false
    det468 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0781_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 69, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0781_orbit
  simpa only [lower69] using h

theorem space0782_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 469), (134, 378), (66, 462), (32, 16), (19, 446), (10, 463)]
    (codeMat 470) (codeMat 179) (codeMat 421) false
    det470 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0782_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0782_orbit
  simpa only [lower69] using h

theorem space0783_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [390, 64, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(390, 16), (64, 192), (32, 36), (19, 350), (10, 427)]
    (codeMat 303) (codeMat 409) (codeMat 473) false
    det303 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0783_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 64, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0783_orbit
  simpa only [lower220] using h

theorem space0784_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 198, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 495), (198, 493), (33, 463), (19, 119), (10, 441)]
    (codeMat 426) (codeMat 241) (codeMat 489) true
    det426 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0784_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 198, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0784_orbit
  simpa only [lower144] using h

theorem space0785_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 199, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (199, 34), (33, 440), (19, 119), (10, 462)]
    (codeMat 298) (codeMat 234) (codeMat 461) true
    det298 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0785_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 199, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0785_orbit
  simpa only [lower144] using h

theorem space0786_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 135, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (135, 34), (33, 463), (19, 441), (10, 119)]
    (codeMat 298) (codeMat 375) (codeMat 491) true
    det298 det375 inv375
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0786_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 135, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0786_orbit
  simpa only [lower144] using h

theorem space0787_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 71, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 32), (71, 34), (33, 118), (19, 462), (10, 441)]
    (codeMat 298) (codeMat 409) (codeMat 473) true
    det298 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0787_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 71, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0787_orbit
  simpa only [lower144] using h

theorem space0788_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [386, 69, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(386, 495), (69, 493), (33, 118), (19, 441), (10, 462)]
    (codeMat 426) (codeMat 431) (codeMat 477) true
    det426 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0788_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 69, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0788_orbit
  simpa only [lower144] using h

theorem space0789_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 192, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (192, 192), (19, 427), (10, 350), (6, 36)]
    (codeMat 311) (codeMat 241) (codeMat 489) false
    det311 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0789_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 192, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0789_orbit
  simpa only [lower220] using h

theorem space0790_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [354, 130, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(354, 334), (130, 192), (19, 245), (10, 350), (6, 36)]
    (codeMat 375) (codeMat 375) (codeMat 491) false
    det375 det375 inv375
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0790_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 130, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0790_orbit
  simpa only [lower220] using h

theorem space0791_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 128, 98, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 11), (128, 1), (98, 213), (19, 113), (10, 446), (6, 16)]
    (codeMat 460) (codeMat 110) (codeMat 444) false
    det460 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0791_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 98, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0791_orbit
  simpa only [lower69] using h

theorem space0792_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 160, 99, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 352), (160, 378), (99, 379), (19, 463), (10, 446), (6, 16)]
    (codeMat 461) (codeMat 478) (codeMat 445) false
    det461 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0792_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 160, 99, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0792_orbit
  simpa only [lower69] using h

theorem space0793_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 96, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 2), (96, 493), (19, 441), (10, 119), (6, 1)]
    (codeMat 481) (codeMat 445) (codeMat 478) true
    det481 det445 inv445
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0793_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 96, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0793_orbit
  simpa only [lower144] using h

theorem space0794_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 162, 66, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (162, 180), (66, 112), (19, 446), (10, 113), (6, 16)]
    (codeMat 270) (codeMat 401) (codeMat 401) false
    det270 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0794_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 162, 66, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0794_orbit
  simpa only [lower69] using h

theorem space0795_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 163, 66, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 352), (163, 165), (66, 112), (19, 463), (10, 113), (6, 16)]
    (codeMat 334) (codeMat 407) (codeMat 405) false
    det334 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0795_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 163, 66, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0795_orbit
  simpa only [lower69] using h

theorem space0796_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 226, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 33), (226, 84), (19, 462), (10, 441), (7, 1)]
    (codeMat 369) (codeMat 234) (codeMat 461) true
    det369 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0796_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 226, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0796_orbit
  simpa only [lower144] using h

theorem space0797_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 225, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (225, 85), (19, 441), (10, 462), (7, 1)]
    (codeMat 305) (codeMat 241) (codeMat 489) true
    det305 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0797_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 225, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0797_orbit
  simpa only [lower144] using h

theorem space0798_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 161, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (161, 492), (19, 119), (10, 441), (7, 1)]
    (codeMat 305) (codeMat 346) (codeMat 459) true
    det305 det346 inv346
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0798_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 161, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0798_orbit
  simpa only [lower144] using h

theorem space0799_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [385, 96, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(385, 33), (96, 493), (19, 441), (10, 119), (7, 1)]
    (codeMat 369) (codeMat 409) (codeMat 473) true
    det369 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0799_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 96, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0799_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
