import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0704_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 163, 98, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 11), (163, 267), (98, 379), (19, 463), (10, 446), (7, 16)]
    (codeMat 270) (codeMat 254) (codeMat 443) false
    det270 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0704_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 163, 98, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0704_orbit
  simpa only [lower69] using h

theorem space0705_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 130, 97, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (130, 1), (97, 196), (19, 113), (10, 463), (6, 16)]
    (codeMat 461) (codeMat 111) (codeMat 412) false
    det461 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0705_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 97, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0705_orbit
  simpa only [lower69] using h

theorem space0706_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 163, 96, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (163, 282), (96, 283), (19, 446), (10, 463), (6, 16)]
    (codeMat 397) (codeMat 473) (codeMat 409) false
    det397 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0706_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 163, 96, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0706_orbit
  simpa only [lower69] using h

theorem space0707_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [294, 128, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(294, 100), (128, 63), (66, 28), (18, 54), (10, 52), (1, 32)]
    (codeMat 87) (codeMat 282) (codeMat 267) true
    det87 det282 inv282
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0707_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 128, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0707_orbit
  simpa only [lower31] using h

theorem space0708_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [450, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(450, 112), (32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    det266 det241 inv241
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0708_lower : 15 ≤ frozenWangTable.L0 (spanCodes [450, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0708_orbit
  simpa only [lower31] using h

theorem space0709_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [294, 166, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(294, 495), (166, 493), (102, 492), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 478) (codeMat 445) false
    det380 det478 inv478
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0709_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 166, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0709_orbit
  simpa only [lower144] using h

theorem space0710_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 164, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (164, 34), (102, 410), (19, 462), (10, 119)]
    (codeMat 359) (codeMat 249) (codeMat 425) false
    det359 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0710_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0710_orbit
  simpa only [lower144] using h

theorem space0711_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [260, 132, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(260, 16), (132, 272), (102, 354), (19, 238), (10, 371)]
    (codeMat 302) (codeMat 185) (codeMat 481) false
    det302 det185 inv185
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0711_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0711_orbit
  simpa only [lower231] using h

theorem space0712_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (128, 1), (102, 84), (19, 462), (10, 441)]
    (codeMat 380) (codeMat 107) (codeMat 428) false
    det380 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0712_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0712_orbit
  simpa only [lower144] using h

theorem space0713_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 129, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 408), (129, 440), (102, 85), (19, 441), (10, 462)]
    (codeMat 359) (codeMat 334) (codeMat 442) false
    det359 det334 inv334
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0713_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0713_orbit
  simpa only [lower144] using h

theorem space0714_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 166, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (166, 411), (100, 35), (19, 462), (10, 119)]
    (codeMat 359) (codeMat 253) (codeMat 415) false
    det359 det253 inv253
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0714_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 166, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0714_orbit
  simpa only [lower144] using h

theorem space0715_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 129, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (129, 440), (99, 84), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 331) (codeMat 410) false
    det303 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0715_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0715_orbit
  simpa only [lower144] using h

theorem space0716_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [288, 166, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(288, 1), (166, 17), (96, 257), (19, 371), (10, 413)]
    (codeMat 302) (codeMat 87) (codeMat 468) false
    det302 det87 inv87
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0716_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0716_orbit
  simpa only [lower231] using h

theorem space0717_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 162, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (162, 35), (96, 411), (19, 119), (10, 462)]
    (codeMat 303) (codeMat 254) (codeMat 443) false
    det303 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0717_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0717_orbit
  simpa only [lower144] using h

theorem space0718_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [293, 163, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(293, 495), (163, 492), (96, 493), (19, 119), (10, 441)]
    (codeMat 317) (codeMat 477) (codeMat 431) false
    det317 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0718_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 163, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0718_orbit
  simpa only [lower144] using h

theorem space0719_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 130, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (130, 1), (96, 411), (19, 462), (10, 119)]
    (codeMat 317) (codeMat 110) (codeMat 444) false
    det317 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0719_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0719_orbit
  simpa only [lower144] using h

theorem space0720_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [263, 129, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(263, 408), (129, 440), (96, 493), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 335) (codeMat 426) false
    det303 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0720_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0720_orbit
  simpa only [lower144] using h

theorem space0721_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 163, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (163, 410), (97, 34), (19, 119), (10, 462)]
    (codeMat 303) (codeMat 250) (codeMat 397) false
    det303 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0721_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 163, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0721_orbit
  simpa only [lower144] using h

theorem space0722_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 132, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (132, 411), (70, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 253) (codeMat 415) false
    det311 det253 inv253
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0722_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 132, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0722_orbit
  simpa only [lower144] using h

theorem space0723_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 129, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (129, 118), (71, 411), (19, 119), (10, 441)]
    (codeMat 311) (codeMat 330) (codeMat 394) false
    det311 det330 inv330
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0723_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 129, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0723_orbit
  simpa only [lower144] using h

theorem space0724_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [256, 163, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(256, 256), (163, 156), (69, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 458) (codeMat 458) false
    det302 det458 inv458
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0724_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0724_orbit
  simpa only [lower231] using h

theorem space0725_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 135, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (135, 411), (69, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 249) (codeMat 425) false
    det311 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0725_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 135, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0725_orbit
  simpa only [lower144] using h

theorem space0726_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [295, 132, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(295, 33), (132, 493), (69, 411), (19, 462), (10, 441)]
    (codeMat 318) (codeMat 478) (codeMat 445) false
    det318 det478 inv478
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0726_lower : 15 ≤ frozenWangTable.L0 (spanCodes [295, 132, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0726_orbit
  simpa only [lower144] using h

theorem space0727_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (131, 118), (69, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 107) (codeMat 428) false
    det318 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0727_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0727_orbit
  simpa only [lower144] using h

theorem space0728_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [290, 129, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(290, 33), (129, 118), (69, 411), (19, 119), (10, 441)]
    (codeMat 311) (codeMat 334) (codeMat 442) false
    det311 det334 inv334
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0728_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 129, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0728_orbit
  simpa only [lower144] using h

theorem space0729_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 132, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (132, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 181) (codeMat 423) false
    det318 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0729_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 132, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0729_orbit
  simpa only [lower144] using h

theorem space0730_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 166, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 408), (166, 493), (67, 440), (19, 119), (10, 441)]
    (codeMat 359) (codeMat 407) (codeMat 405) false
    det359 det407 inv407
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0730_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 166, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0730_orbit
  simpa only [lower144] using h

theorem space0731_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 165, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (165, 84), (67, 440), (19, 119), (10, 441)]
    (codeMat 359) (codeMat 403) (codeMat 403) false
    det359 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0731_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 165, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0731_orbit
  simpa only [lower144] using h

theorem space0732_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [262, 163, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(262, 408), (163, 85), (67, 440), (19, 462), (10, 441)]
    (codeMat 303) (codeMat 405) (codeMat 407) false
    det303 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0732_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 163, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0732_orbit
  simpa only [lower144] using h

theorem space0733_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 161, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (161, 492), (67, 440), (19, 462), (10, 441)]
    (codeMat 303) (codeMat 401) (codeMat 401) false
    det303 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0733_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0733_orbit
  simpa only [lower144] using h

theorem space0734_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 133, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (133, 493), (67, 118), (19, 462), (10, 119)]
    (codeMat 311) (codeMat 403) (codeMat 403) false
    det311 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0734_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0734_orbit
  simpa only [lower144] using h

theorem space0735_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 166, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (166, 411), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 181) (codeMat 423) false
    det380 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0735_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 166, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0735_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
