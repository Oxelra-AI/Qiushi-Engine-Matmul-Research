import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0256_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 195, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (195, 192), (38, 399), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 501) (codeMat 494) false
    det359 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0256_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 195, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0256_orbit
  simpa only [lower220] using h

theorem space0257_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 128, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (128, 192), (33, 378), (19, 427), (10, 245)]
    (codeMat 303) (codeMat 115) (codeMat 492) false
    det303 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0257_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0257_orbit
  simpa only [lower220] using h

theorem space0258_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 193, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (193, 414), (33, 378), (19, 245), (10, 427)]
    (codeMat 431) (codeMat 501) (codeMat 494) false
    det431 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0258_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 193, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0258_orbit
  simpa only [lower220] using h

theorem space0259_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 133, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (133, 493), (32, 1), (19, 462), (10, 119)]
    (codeMat 482) (codeMat 94) (codeMat 500) true
    det482 det94 inv94
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0259_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0259_orbit
  simpa only [lower144] using h

theorem space0260_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 192, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (192, 192), (32, 36), (19, 245), (10, 350)]
    (codeMat 303) (codeMat 458) (codeMat 458) false
    det303 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0260_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 192, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0260_orbit
  simpa only [lower220] using h

theorem space0261_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 133, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 495), (133, 493), (35, 463), (19, 462), (10, 119)]
    (codeMat 426) (codeMat 122) (codeMat 460) true
    det426 det122 inv122
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0261_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0261_orbit
  simpa only [lower144] using h

theorem space0262_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (134, 34), (35, 440), (19, 441), (10, 119)]
    (codeMat 298) (codeMat 115) (codeMat 492) true
    det298 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0262_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0262_orbit
  simpa only [lower144] using h

theorem space0263_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [321, 199, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(321, 495), (199, 493), (35, 118), (19, 119), (10, 441)]
    (codeMat 426) (codeMat 501) (codeMat 494) true
    det426 det501 inv501
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0263_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 199, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0263_orbit
  simpa only [lower144] using h

theorem space0264_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 198, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (198, 34), (35, 118), (19, 119), (10, 462)]
    (codeMat 298) (codeMat 458) (codeMat 458) true
    det298 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0264_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 198, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0264_orbit
  simpa only [lower144] using h

theorem space0265_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 131, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (131, 414), (34, 209), (19, 350), (10, 245)]
    (codeMat 431) (codeMat 122) (codeMat 460) false
    det431 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0265_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0265_orbit
  simpa only [lower220] using h

theorem space0266_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 199, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (199, 493), (34, 440), (19, 119), (10, 441)]
    (codeMat 482) (codeMat 465) (codeMat 465) true
    det482 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0266_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 199, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0266_orbit
  simpa only [lower144] using h

theorem space0267_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 128, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (128, 192), (19, 245), (10, 427), (5, 36)]
    (codeMat 311) (codeMat 122) (codeMat 460) false
    det311 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0267_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0267_orbit
  simpa only [lower220] using h

theorem space0268_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 224, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (224, 493), (19, 462), (10, 441), (5, 1)]
    (codeMat 481) (codeMat 494) (codeMat 501) true
    det481 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0268_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 224, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0268_orbit
  simpa only [lower144] using h

theorem space0269_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 161, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (161, 84), (19, 119), (10, 462), (4, 1)]
    (codeMat 481) (codeMat 87) (codeMat 468) true
    det481 det87 inv87
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0269_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 161, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0269_orbit
  simpa only [lower144] using h

theorem space0270_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [354, 195, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(354, 443), (195, 192), (19, 350), (10, 427), (4, 36)]
    (codeMat 375) (codeMat 458) (codeMat 458) false
    det375 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0270_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 195, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0270_orbit
  simpa only [lower220] using h

theorem space0271_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 130, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (130, 192), (19, 245), (10, 350), (7, 36)]
    (codeMat 375) (codeMat 115) (codeMat 492) false
    det375 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0271_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 130, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0271_orbit
  simpa only [lower220] using h

theorem space0272_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [354, 192, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(354, 334), (192, 192), (19, 427), (10, 350), (7, 36)]
    (codeMat 311) (codeMat 501) (codeMat 494) false
    det311 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0272_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 192, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0272_orbit
  simpa only [lower220] using h

theorem space0273_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 161, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 33), (161, 84), (19, 119), (10, 462), (6, 1)]
    (codeMat 369) (codeMat 115) (codeMat 492) true
    det369 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0273_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 161, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0273_orbit
  simpa only [lower144] using h

theorem space0274_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 163, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (163, 85), (19, 119), (10, 441), (6, 1)]
    (codeMat 305) (codeMat 122) (codeMat 460) true
    det305 det122 inv122
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0274_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0274_orbit
  simpa only [lower144] using h

theorem space0275_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [323, 224, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(323, 33), (224, 493), (19, 462), (10, 441), (6, 1)]
    (codeMat 369) (codeMat 458) (codeMat 458) true
    det369 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0275_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 224, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0275_orbit
  simpa only [lower144] using h

theorem space0276_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 227, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (227, 411), (19, 441), (10, 462), (6, 1)]
    (codeMat 305) (codeMat 501) (codeMat 494) true
    det305 det501 inv501
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0276_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 227, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0276_orbit
  simpa only [lower144] using h

theorem space0277_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 130, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 208), (130, 192), (38, 209), (19, 427), (10, 350)]
    (codeMat 359) (codeMat 94) (codeMat 500) false
    det359 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0277_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0277_orbit
  simpa only [lower220] using h

theorem space0278_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [321, 193, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(321, 398), (193, 414), (38, 378), (19, 427), (10, 245)]
    (codeMat 423) (codeMat 494) (codeMat 501) false
    det423 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0278_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 193, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0278_orbit
  simpa only [lower220] using h

theorem space0279_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (134, 34), (32, 1), (19, 441), (10, 119)]
    (codeMat 354) (codeMat 87) (codeMat 468) true
    det354 det87 inv87
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0279_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0279_orbit
  simpa only [lower144] using h

theorem space0280_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [327, 193, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(327, 398), (193, 414), (32, 36), (19, 245), (10, 427)]
    (codeMat 431) (codeMat 465) (codeMat 465) false
    det431 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0280_lower : 15 ≤ frozenWangTable.L0 (spanCodes [327, 193, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0280_orbit
  simpa only [lower220] using h

theorem space0281_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [289, 130, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(289, 37), (130, 192), (19, 245), (10, 350), (5, 36)]
    (codeMat 375) (codeMat 87) (codeMat 468) false
    det375 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0281_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 130, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0281_orbit
  simpa only [lower220] using h

theorem space0282_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 227, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (227, 411), (19, 441), (10, 462), (5, 1)]
    (codeMat 417) (codeMat 465) (codeMat 465) true
    det417 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0282_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 227, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0282_orbit
  simpa only [lower144] using h

theorem space0283_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [385, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(385, 80), (33, 20), (17, 21), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    det266 det394 inv394
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0283_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0283_orbit
  simpa only [lower31] using h

theorem space0284_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 131, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 398), (131, 414), (39, 399), (19, 350), (10, 427)]
    (codeMat 423) (codeMat 87) (codeMat 468) false
    det423 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0284_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0284_orbit
  simpa only [lower220] using h

theorem space0285_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 197, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (197, 34), (39, 118), (19, 462), (10, 119)]
    (codeMat 299) (codeMat 465) (codeMat 465) true
    det299 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0285_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 197, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0285_orbit
  simpa only [lower144] using h

theorem space0286_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [261, 131, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(261, 398), (131, 414), (33, 399), (19, 350), (10, 245)]
    (codeMat 431) (codeMat 94) (codeMat 500) false
    det431 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0286_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0286_orbit
  simpa only [lower220] using h

theorem space0287_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [326, 192, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(326, 208), (192, 192), (33, 399), (19, 245), (10, 350)]
    (codeMat 303) (codeMat 494) (codeMat 501) false
    det303 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0287_lower : 15 ≤ frozenWangTable.L0 (spanCodes [326, 192, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0287_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
