import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0192_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 65, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (65, 192), (19, 427), (10, 245), (6, 36)]
    (codeMat 375) (codeMat 185) (codeMat 481) false
    det375 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0192_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 65, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0192_orbit
  simpa only [lower220] using h

theorem space0193_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 99, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 33), (99, 84), (19, 441), (10, 119), (5, 1)]
    (codeMat 369) (codeMat 185) (codeMat 481) true
    det369 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0193_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 99, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0193_orbit
  simpa only [lower144] using h

theorem space0194_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 98, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (98, 85), (19, 462), (10, 119), (5, 1)]
    (codeMat 305) (codeMat 171) (codeMat 485) true
    det305 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0194_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 98, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0194_orbit
  simpa only [lower144] using h

theorem space0195_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 99, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (99, 84), (19, 441), (10, 119), (4, 1)]
    (codeMat 481) (codeMat 157) (codeMat 486) true
    det481 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0195_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 99, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0195_orbit
  simpa only [lower144] using h

theorem space0196_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (160, 34), (19, 119), (10, 441), (4, 1)]
    (codeMat 305) (codeMat 94) (codeMat 500) true
    det305 det94 inv94
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0196_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0196_orbit
  simpa only [lower144] using h

theorem space0197_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [321, 193, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(321, 37), (193, 53), (19, 427), (10, 350), (4, 36)]
    (codeMat 421) (codeMat 465) (codeMat 465) false
    det421 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0197_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 193, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0197_orbit
  simpa only [lower220] using h

theorem space0198_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 129, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 37), (129, 53), (19, 245), (10, 350), (5, 36)]
    (codeMat 485) (codeMat 87) (codeMat 468) false
    det485 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0198_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0198_orbit
  simpa only [lower220] using h

theorem space0199_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 226, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 460), (226, 492), (19, 441), (10, 462), (5, 1)]
    (codeMat 305) (codeMat 465) (codeMat 465) true
    det305 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0199_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 226, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0199_orbit
  simpa only [lower144] using h

theorem space0200_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [290, 162, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(290, 33), (162, 35), (19, 119), (10, 462), (6, 1)]
    (codeMat 481) (codeMat 115) (codeMat 492) true
    det481 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0200_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 162, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0200_orbit
  simpa only [lower144] using h

theorem space0201_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (160, 34), (19, 119), (10, 441), (6, 1)]
    (codeMat 417) (codeMat 122) (codeMat 460) true
    det417 det122 inv122
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0201_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0201_orbit
  simpa only [lower144] using h

theorem space0202_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 226, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 494), (226, 492), (19, 441), (10, 462), (6, 1)]
    (codeMat 417) (codeMat 501) (codeMat 494) true
    det417 det501 inv501
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0202_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 226, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0202_orbit
  simpa only [lower144] using h

theorem space0203_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [353, 225, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(353, 408), (225, 410), (19, 462), (10, 441), (6, 1)]
    (codeMat 481) (codeMat 458) (codeMat 458) true
    det481 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0203_lower : 15 ≤ frozenWangTable.L0 (spanCodes [353, 225, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0203_orbit
  simpa only [lower144] using h

theorem space0204_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 129, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (129, 53), (19, 245), (10, 350), (7, 36)]
    (codeMat 485) (codeMat 115) (codeMat 492) false
    det485 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0204_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0204_orbit
  simpa only [lower220] using h

theorem space0205_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 193, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (193, 53), (19, 427), (10, 350), (7, 36)]
    (codeMat 421) (codeMat 501) (codeMat 494) false
    det421 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0205_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 193, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0205_orbit
  simpa only [lower220] using h

theorem space0206_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 162, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (162, 35), (19, 119), (10, 462), (4, 1)]
    (codeMat 369) (codeMat 87) (codeMat 468) true
    det369 det87 inv87
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0206_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 162, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0206_orbit
  simpa only [lower144] using h

theorem space0207_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 194, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (194, 53), (19, 350), (10, 427), (4, 36)]
    (codeMat 485) (codeMat 458) (codeMat 458) false
    det485 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0207_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 194, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0207_orbit
  simpa only [lower220] using h

theorem space0208_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 131, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (131, 53), (19, 245), (10, 427), (5, 36)]
    (codeMat 421) (codeMat 122) (codeMat 460) false
    det421 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0208_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0208_orbit
  simpa only [lower220] using h

theorem space0209_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 225, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 443), (225, 410), (19, 462), (10, 441), (5, 1)]
    (codeMat 369) (codeMat 494) (codeMat 501) true
    det369 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0209_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 225, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0209_orbit
  simpa only [lower144] using h

theorem space0210_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 131, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 37), (131, 53), (19, 245), (10, 427), (7, 36)]
    (codeMat 421) (codeMat 94) (codeMat 500) false
    det421 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0210_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0210_orbit
  simpa only [lower220] using h

theorem space0211_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [322, 194, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(322, 37), (194, 53), (19, 350), (10, 427), (7, 36)]
    (codeMat 485) (codeMat 494) (codeMat 501) false
    det485 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0211_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 194, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0211_orbit
  simpa only [lower220] using h

theorem space0212_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (132, 34), (32, 1), (19, 441), (10, 119)]
    (codeMat 298) (codeMat 87) (codeMat 468) true
    det298 det87 inv87
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0212_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0212_orbit
  simpa only [lower144] using h

theorem space0213_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [322, 194, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(322, 398), (194, 414), (32, 36), (19, 245), (10, 427)]
    (codeMat 486) (codeMat 465) (codeMat 465) false
    det486 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0213_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 194, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0213_orbit
  simpa only [lower220] using h

theorem space0214_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [262, 128, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(262, 208), (128, 192), (38, 209), (19, 427), (10, 350)]
    (codeMat 302) (codeMat 94) (codeMat 500) false
    det302 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0214_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0214_orbit
  simpa only [lower220] using h

theorem space0215_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [324, 194, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(324, 398), (194, 414), (38, 378), (19, 427), (10, 245)]
    (codeMat 494) (codeMat 494) (codeMat 501) false
    det494 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0215_lower : 15 ≤ frozenWangTable.L0 (spanCodes [324, 194, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0215_orbit
  simpa only [lower220] using h

theorem space0216_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 129, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 398), (129, 414), (33, 399), (19, 350), (10, 245)]
    (codeMat 486) (codeMat 94) (codeMat 500) false
    det486 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0216_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0216_orbit
  simpa only [lower220] using h

theorem space0217_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [323, 195, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(323, 208), (195, 192), (33, 399), (19, 245), (10, 350)]
    (codeMat 358) (codeMat 494) (codeMat 501) false
    det358 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0217_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 195, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0217_orbit
  simpa only [lower220] using h

theorem space0218_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [263, 129, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(263, 398), (129, 414), (39, 399), (19, 350), (10, 427)]
    (codeMat 494) (codeMat 87) (codeMat 468) false
    det494 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0218_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0218_orbit
  simpa only [lower220] using h

theorem space0219_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 198, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (198, 34), (39, 118), (19, 462), (10, 119)]
    (codeMat 355) (codeMat 465) (codeMat 465) true
    det355 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0219_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 198, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0219_orbit
  simpa only [lower144] using h

theorem space0220_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 130, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 208), (130, 192), (34, 209), (19, 427), (10, 245)]
    (codeMat 358) (codeMat 87) (codeMat 468) false
    det358 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0220_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0220_orbit
  simpa only [lower220] using h

theorem space0221_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 197, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (197, 34), (34, 463), (19, 119), (10, 462)]
    (codeMat 298) (codeMat 494) (codeMat 501) true
    det298 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0221_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 197, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0221_orbit
  simpa only [lower144] using h

theorem space0222_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (134, 34), (36, 1), (19, 441), (10, 462)]
    (codeMat 355) (codeMat 94) (codeMat 500) true
    det355 det94 inv94
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0222_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0222_orbit
  simpa only [lower144] using h

theorem space0223_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [326, 192, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(326, 208), (192, 192), (36, 36), (19, 350), (10, 245)]
    (codeMat 302) (codeMat 465) (codeMat 465) false
    det302 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0223_lower : 15 ≤ frozenWangTable.L0 (spanCodes [326, 192, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0223_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
