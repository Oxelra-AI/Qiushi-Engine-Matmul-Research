import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0288_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [355, 192, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(355, 379), (192, 192), (19, 427), (10, 350), (4, 36)]
    (codeMat 311) (codeMat 465) (codeMat 465) false
    det311 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0288_lower : 15 ≤ frozenWangTable.L0 (spanCodes [355, 192, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0288_orbit
  simpa only [lower220] using h

theorem space0289_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [385, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(385, 112), (32, 2), (16, 3), (9, 54), (5, 32), (3, 40)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    det266 det122 inv122
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0289_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0289_orbit
  simpa only [lower31] using h

theorem space0290_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [386, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(386, 120), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    det266 det498 inv498
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0290_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0290_orbit
  simpa only [lower31] using h

theorem space0291_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (132, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 401) (codeMat 401) false
    det428 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0291_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0291_orbit
  simpa only [lower144] using h

theorem space0292_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [261, 133, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(261, 33), (133, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 405) (codeMat 407) false
    det428 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0292_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0292_orbit
  simpa only [lower144] using h

theorem space0293_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (160, 35), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 403) (codeMat 403) false
    det372 det403 inv403
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0293_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0293_orbit
  simpa only [lower144] using h

theorem space0294_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [290, 162, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(290, 495), (162, 493), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 407) (codeMat 405) false
    det372 det407 inv407
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0294_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 162, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0294_orbit
  simpa only [lower144] using h

theorem space0295_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 164, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (164, 34), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 401) (codeMat 401) false
    det380 det401 inv401
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0295_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0295_orbit
  simpa only [lower144] using h

theorem space0296_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [295, 167, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(295, 495), (167, 492), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 405) (codeMat 407) false
    det380 det405 inv405
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0296_lower : 15 ≤ frozenWangTable.L0 (spanCodes [295, 167, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0296_orbit
  simpa only [lower144] using h

theorem space0297_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 133, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (133, 35), (65, 1), (19, 462), (10, 119)]
    (codeMat 421) (codeMat 179) (codeMat 421) false
    det421 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0297_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0297_orbit
  simpa only [lower144] using h

theorem space0298_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 162, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (162, 411), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 181) (codeMat 423) false
    det358 det181 inv181
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0298_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 162, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0298_orbit
  simpa only [lower144] using h

theorem space0299_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 167, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (167, 410), (67, 440), (19, 119), (10, 441)]
    (codeMat 359) (codeMat 179) (codeMat 421) false
    det359 det179 inv179
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0299_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 167, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0299_orbit
  simpa only [lower144] using h

theorem space0300_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 128, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (128, 1), (68, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 331) (codeMat 410) false
    det428 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0300_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0300_orbit
  simpa only [lower144] using h

theorem space0301_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 133, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (133, 35), (69, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 250) (codeMat 397) false
    det428 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0301_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0301_orbit
  simpa only [lower144] using h

theorem space0302_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [262, 128, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(262, 33), (128, 1), (70, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 335) (codeMat 426) false
    det428 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0302_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0302_orbit
  simpa only [lower144] using h

theorem space0303_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 130, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (130, 1), (70, 34), (19, 119), (10, 441)]
    (codeMat 421) (codeMat 110) (codeMat 444) false
    det421 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0303_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0303_orbit
  simpa only [lower144] using h

theorem space0304_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 133, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 33), (133, 34), (70, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 477) (codeMat 431) false
    det421 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0304_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0304_orbit
  simpa only [lower144] using h

theorem space0305_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (134, 35), (70, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 254) (codeMat 443) false
    det428 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0305_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0305_orbit
  simpa only [lower144] using h

theorem space0306_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [292, 162, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(292, 511), (162, 495), (70, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 494) (codeMat 501) false
    det302 det494 inv494
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0306_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0306_orbit
  simpa only [lower231] using h

theorem space0307_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 128, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (128, 1), (96, 34), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 330) (codeMat 394) false
    det372 det330 inv330
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0307_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0307_orbit
  simpa only [lower144] using h

theorem space0308_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [291, 128, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(291, 495), (128, 1), (99, 492), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 334) (codeMat 442) false
    det372 det334 inv334
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0308_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 128, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0308_orbit
  simpa only [lower144] using h

theorem space0309_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (131, 440), (99, 410), (19, 441), (10, 119)]
    (codeMat 358) (codeMat 107) (codeMat 428) false
    det358 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0309_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0309_orbit
  simpa only [lower144] using h

theorem space0310_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 162, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 408), (162, 493), (99, 85), (19, 119), (10, 462)]
    (codeMat 358) (codeMat 478) (codeMat 445) false
    det358 det478 inv478
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0310_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0310_orbit
  simpa only [lower144] using h

theorem space0311_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 163, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (163, 85), (99, 84), (19, 119), (10, 441)]
    (codeMat 372) (codeMat 249) (codeMat 425) false
    det372 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0311_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0311_orbit
  simpa only [lower144] using h

theorem space0312_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [260, 167, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(260, 16), (167, 354), (99, 114), (19, 371), (10, 413)]
    (codeMat 302) (codeMat 115) (codeMat 492) false
    det302 det115 inv115
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0312_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 167, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0312_orbit
  simpa only [lower231] using h

theorem space0313_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 128, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (128, 1), (100, 35), (19, 462), (10, 441)]
    (codeMat 380) (codeMat 331) (codeMat 410) false
    det380 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0313_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 128, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0313_orbit
  simpa only [lower144] using h

theorem space0314_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [293, 128, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(293, 495), (128, 1), (101, 493), (19, 462), (10, 441)]
    (codeMat 380) (codeMat 335) (codeMat 426) false
    det380 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0314_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 128, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0314_orbit
  simpa only [lower144] using h

theorem space0315_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 129, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (129, 440), (101, 411), (19, 441), (10, 462)]
    (codeMat 359) (codeMat 110) (codeMat 444) false
    det359 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0315_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 129, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0315_orbit
  simpa only [lower144] using h

theorem space0316_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [288, 133, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(288, 1), (133, 272), (101, 17), (19, 238), (10, 371)]
    (codeMat 302) (codeMat 157) (codeMat 486) false
    det302 det157 inv157
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0316_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0316_orbit
  simpa only [lower231] using h

theorem space0317_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 165, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (165, 410), (101, 411), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 254) (codeMat 443) false
    det380 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0317_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 165, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0317_orbit
  simpa only [lower144] using h

theorem space0318_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 167, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 408), (167, 85), (101, 493), (19, 462), (10, 119)]
    (codeMat 359) (codeMat 477) (codeMat 431) false
    det359 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0318_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 167, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0318_orbit
  simpa only [lower144] using h

theorem space0319_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 167, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (167, 84), (103, 85), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 250) (codeMat 397) false
    det380 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0319_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 167, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0319_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
