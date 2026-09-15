import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0224_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [263, 135, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(263, 495), (135, 493), (35, 463), (19, 462), (10, 119)]
    (codeMat 482) (codeMat 122) (codeMat 460) true
    det482 det122 inv122
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0224_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0224_orbit
  simpa only [lower144] using h

theorem space0225_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (132, 34), (35, 440), (19, 441), (10, 119)]
    (codeMat 354) (codeMat 115) (codeMat 492) true
    det354 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0225_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0225_orbit
  simpa only [lower144] using h

theorem space0226_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 197, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 32), (197, 34), (35, 118), (19, 119), (10, 462)]
    (codeMat 354) (codeMat 458) (codeMat 458) true
    det354 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0226_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 197, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0226_orbit
  simpa only [lower144] using h

theorem space0227_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [324, 196, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(324, 495), (196, 493), (35, 118), (19, 119), (10, 441)]
    (codeMat 482) (codeMat 501) (codeMat 494) true
    det482 det501 inv501
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0227_lower : 15 ≤ frozenWangTable.L0 (spanCodes [324, 196, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0227_orbit
  simpa only [lower144] using h

theorem space0228_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 129, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (129, 414), (34, 209), (19, 350), (10, 245)]
    (codeMat 486) (codeMat 122) (codeMat 460) false
    det486 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0228_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0228_orbit
  simpa only [lower220] using h

theorem space0229_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 196, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (196, 493), (34, 440), (19, 119), (10, 441)]
    (codeMat 426) (codeMat 465) (codeMat 465) true
    det426 det465 inv465
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0229_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 196, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0229_orbit
  simpa only [lower144] using h

theorem space0230_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 130, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (130, 192), (33, 378), (19, 427), (10, 245)]
    (codeMat 358) (codeMat 115) (codeMat 492) false
    det358 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0230_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0230_orbit
  simpa only [lower220] using h

theorem space0231_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 194, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (194, 414), (33, 378), (19, 245), (10, 427)]
    (codeMat 486) (codeMat 501) (codeMat 494) false
    det486 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0231_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 194, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0231_orbit
  simpa only [lower220] using h

theorem space0232_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 135, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (135, 493), (32, 1), (19, 462), (10, 119)]
    (codeMat 426) (codeMat 94) (codeMat 500) true
    det426 det94 inv94
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0232_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0232_orbit
  simpa only [lower144] using h

theorem space0233_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 195, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (195, 192), (32, 36), (19, 245), (10, 350)]
    (codeMat 358) (codeMat 458) (codeMat 458) false
    det358 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0233_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 195, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0233_orbit
  simpa only [lower220] using h

theorem space0234_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 128, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (128, 192), (39, 378), (19, 427), (10, 350)]
    (codeMat 302) (codeMat 122) (codeMat 460) false
    det302 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0234_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0234_orbit
  simpa only [lower220] using h

theorem space0235_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 196, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (196, 493), (39, 118), (19, 441), (10, 119)]
    (codeMat 419) (codeMat 494) (codeMat 501) true
    det419 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0235_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 196, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0235_orbit
  simpa only [lower144] using h

theorem space0236_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 129, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (129, 414), (38, 209), (19, 350), (10, 427)]
    (codeMat 494) (codeMat 115) (codeMat 492) false
    det494 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0236_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0236_orbit
  simpa only [lower220] using h

theorem space0237_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 192, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (192, 192), (38, 399), (19, 350), (10, 245)]
    (codeMat 302) (codeMat 501) (codeMat 494) false
    det302 det501 inv501
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0237_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 192, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0237_orbit
  simpa only [lower220] using h

theorem space0238_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [257, 135, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(257, 495), (135, 493), (37, 463), (19, 462), (10, 441)]
    (codeMat 491) (codeMat 115) (codeMat 492) true
    det491 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0238_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0238_orbit
  simpa only [lower144] using h

theorem space0239_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [322, 196, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(322, 495), (196, 493), (37, 440), (19, 441), (10, 119)]
    (codeMat 491) (codeMat 458) (codeMat 458) true
    det491 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0239_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 196, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0239_orbit
  simpa only [lower144] using h

theorem space0240_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 135, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (135, 493), (36, 1), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 87) (codeMat 468) true
    det419 det87 inv87
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0240_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0240_orbit
  simpa only [lower144] using h

theorem space0241_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [325, 194, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(325, 16), (194, 414), (36, 36), (19, 427), (10, 245)]
    (codeMat 494) (codeMat 458) (codeMat 458) false
    det494 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0241_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 194, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0241_orbit
  simpa only [lower220] using h

theorem space0242_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (132, 34), (36, 1), (19, 441), (10, 462)]
    (codeMat 299) (codeMat 94) (codeMat 500) true
    det299 det94 inv94
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0242_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0242_orbit
  simpa only [lower144] using h

theorem space0243_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [323, 195, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(323, 208), (195, 192), (36, 36), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 465) (codeMat 465) false
    det359 det465 inv465
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0243_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 195, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0243_orbit
  simpa only [lower220] using h

theorem space0244_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [262, 128, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(262, 208), (128, 192), (34, 209), (19, 427), (10, 245)]
    (codeMat 303) (codeMat 87) (codeMat 468) false
    det303 det87 inv87
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0244_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0244_orbit
  simpa only [lower220] using h

theorem space0245_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 198, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (198, 34), (34, 463), (19, 119), (10, 462)]
    (codeMat 354) (codeMat 494) (codeMat 501) true
    det354 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0245_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 198, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0245_orbit
  simpa only [lower144] using h

theorem space0246_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [291, 128, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(291, 37), (128, 192), (19, 245), (10, 427), (7, 36)]
    (codeMat 311) (codeMat 94) (codeMat 500) false
    det311 det94 inv94
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0246_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 128, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0246_orbit
  simpa only [lower220] using h

theorem space0247_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [352, 195, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(352, 398), (195, 192), (19, 350), (10, 427), (7, 36)]
    (codeMat 375) (codeMat 494) (codeMat 501) false
    det375 det494 inv494
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0247_lower : 15 ≤ frozenWangTable.L0 (spanCodes [352, 195, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0247_orbit
  simpa only [lower220] using h

theorem space0248_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [261, 133, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(261, 495), (133, 493), (37, 463), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 115) (codeMat 492) true
    det419 det115 inv115
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0248_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0248_orbit
  simpa only [lower144] using h

theorem space0249_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (132, 34), (37, 440), (19, 441), (10, 462)]
    (codeMat 355) (codeMat 122) (codeMat 460) true
    det355 det122 inv122
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0249_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0249_orbit
  simpa only [lower144] using h

theorem space0250_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 197, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 32), (197, 34), (37, 463), (19, 462), (10, 119)]
    (codeMat 355) (codeMat 501) (codeMat 494) true
    det355 det501 inv501
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0250_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 197, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0250_orbit
  simpa only [lower144] using h

theorem space0251_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [327, 199, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(327, 495), (199, 493), (37, 440), (19, 441), (10, 119)]
    (codeMat 419) (codeMat 458) (codeMat 458) true
    det419 det458 inv458
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0251_lower : 15 ≤ frozenWangTable.L0 (spanCodes [327, 199, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0251_orbit
  simpa only [lower144] using h

theorem space0252_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [320, 193, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(320, 16), (193, 414), (36, 36), (19, 427), (10, 245)]
    (codeMat 423) (codeMat 458) (codeMat 458) false
    det423 det458 inv458
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0252_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 193, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0252_orbit
  simpa only [lower220] using h

theorem space0253_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 130, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (130, 192), (39, 378), (19, 427), (10, 350)]
    (codeMat 359) (codeMat 122) (codeMat 460) false
    det359 det122 inv122
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0253_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0253_orbit
  simpa only [lower220] using h

theorem space0254_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 199, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (199, 493), (39, 118), (19, 441), (10, 119)]
    (codeMat 491) (codeMat 494) (codeMat 501) true
    det491 det494 inv494
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0254_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 199, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0254_orbit
  simpa only [lower144] using h

theorem space0255_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 131, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (131, 414), (38, 209), (19, 350), (10, 427)]
    (codeMat 423) (codeMat 115) (codeMat 492) false
    det423 det115 inv115
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0255_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0255_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
