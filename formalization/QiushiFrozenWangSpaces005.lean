import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0160_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 65, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (65, 192), (35, 378), (19, 350), (10, 427)]
    (codeMat 358) (codeMat 185) (codeMat 481) false
    det358 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0160_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 65, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0160_orbit
  simpa only [lower220] using h

theorem space0161_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 70, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (70, 493), (32, 1), (19, 441), (10, 462)]
    (codeMat 426) (codeMat 143) (codeMat 482) true
    det426 det143 inv143
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0161_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 70, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0161_orbit
  simpa only [lower144] using h

theorem space0162_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 67, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (67, 414), (33, 209), (19, 427), (10, 350)]
    (codeMat 486) (codeMat 171) (codeMat 485) false
    det486 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0162_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 67, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0162_orbit
  simpa only [lower220] using h

theorem space0163_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 64, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (64, 192), (38, 378), (19, 245), (10, 427)]
    (codeMat 302) (codeMat 171) (codeMat 485) false
    det302 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0163_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 64, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0163_orbit
  simpa only [lower220] using h

theorem space0164_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 70, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 495), (70, 493), (39, 463), (19, 119), (10, 462)]
    (codeMat 491) (codeMat 185) (codeMat 481) true
    det491 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0164_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 70, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0164_orbit
  simpa only [lower144] using h

theorem space0165_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 69, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (69, 34), (39, 440), (19, 119), (10, 441)]
    (codeMat 299) (codeMat 171) (codeMat 485) true
    det299 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0165_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 69, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0165_orbit
  simpa only [lower144] using h

theorem space0166_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 70, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (70, 493), (36, 1), (19, 119), (10, 462)]
    (codeMat 419) (codeMat 157) (codeMat 486) true
    det419 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0166_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 70, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0166_orbit
  simpa only [lower144] using h

theorem space0167_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 67, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (67, 414), (37, 209), (19, 245), (10, 350)]
    (codeMat 494) (codeMat 185) (codeMat 481) false
    det494 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0167_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 67, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0167_orbit
  simpa only [lower220] using h

theorem space0168_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 67, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 398), (67, 414), (35, 399), (19, 427), (10, 350)]
    (codeMat 486) (codeMat 143) (codeMat 482) false
    det486 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0168_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 67, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0168_orbit
  simpa only [lower220] using h

theorem space0169_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [262, 67, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(262, 398), (67, 414), (38, 399), (19, 245), (10, 350)]
    (codeMat 494) (codeMat 157) (codeMat 486) false
    det494 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0169_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 67, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0169_orbit
  simpa only [lower220] using h

theorem space0170_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [261, 64, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(261, 208), (64, 192), (33, 209), (19, 350), (10, 427)]
    (codeMat 303) (codeMat 157) (codeMat 486) false
    det303 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0170_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 64, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0170_orbit
  simpa only [lower220] using h

theorem space0171_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [290, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(290, 37), (64, 192), (19, 350), (10, 245), (6, 36)]
    (codeMat 311) (codeMat 143) (codeMat 482) false
    det311 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0171_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0171_orbit
  simpa only [lower220] using h

theorem space0172_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 65, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 208), (65, 192), (37, 209), (19, 245), (10, 427)]
    (codeMat 359) (codeMat 143) (codeMat 482) false
    det359 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0172_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 65, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0172_orbit
  simpa only [lower220] using h

theorem space0173_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 69, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (69, 34), (32, 1), (19, 462), (10, 441)]
    (codeMat 354) (codeMat 157) (codeMat 486) true
    det354 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0173_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 69, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0173_orbit
  simpa only [lower144] using h

theorem space0174_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [291, 65, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(291, 37), (65, 192), (19, 427), (10, 245), (7, 36)]
    (codeMat 375) (codeMat 157) (codeMat 486) false
    det375 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0174_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 65, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0174_orbit
  simpa only [lower220] using h

theorem space0175_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [322, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(322, 112), (34, 52), (18, 54), (10, 53), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 465) (codeMat 465) false
    det266 det465 inv465
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0175_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0175_orbit
  simpa only [lower31] using h

theorem space0176_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 398), (66, 414), (38, 399), (19, 245), (10, 350)]
    (codeMat 423) (codeMat 157) (codeMat 486) false
    det423 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0176_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0176_orbit
  simpa only [lower220] using h

theorem space0177_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [263, 66, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(263, 398), (66, 414), (35, 399), (19, 427), (10, 350)]
    (codeMat 431) (codeMat 143) (codeMat 482) false
    det431 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0177_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 66, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0177_orbit
  simpa only [lower220] using h

theorem space0178_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 98, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (98, 85), (19, 462), (10, 119), (4, 1)]
    (codeMat 417) (codeMat 143) (codeMat 482) true
    det417 det143 inv143
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0178_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 98, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0178_orbit
  simpa only [lower144] using h

theorem space0179_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [321, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(321, 88), (32, 2), (17, 28), (8, 3), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 169) (codeMat 225) false
    det266 det169 inv169
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0179_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0179_orbit
  simpa only [lower31] using h

theorem space0180_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [321, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(321, 120), (33, 62), (16, 2), (9, 63), (5, 8), (3, 40)]
    (codeMat 266) (codeMat 377) (codeMat 369) false
    det266 det377 inv377
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0180_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0180_orbit
  simpa only [lower31] using h

theorem space0181_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [263, 71, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(263, 495), (71, 493), (39, 463), (19, 119), (10, 462)]
    (codeMat 419) (codeMat 185) (codeMat 481) true
    det419 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0181_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 71, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0181_orbit
  simpa only [lower144] using h

theorem space0182_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 68, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (68, 34), (39, 440), (19, 119), (10, 441)]
    (codeMat 355) (codeMat 171) (codeMat 485) true
    det355 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0182_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 68, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0182_orbit
  simpa only [lower144] using h

theorem space0183_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 65, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (65, 192), (38, 378), (19, 245), (10, 427)]
    (codeMat 359) (codeMat 171) (codeMat 485) false
    det359 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0183_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 65, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0183_orbit
  simpa only [lower220] using h

theorem space0184_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 66, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (66, 414), (37, 209), (19, 245), (10, 350)]
    (codeMat 423) (codeMat 185) (codeMat 481) false
    det423 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0184_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 66, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0184_orbit
  simpa only [lower220] using h

theorem space0185_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 71, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (71, 493), (36, 1), (19, 119), (10, 462)]
    (codeMat 491) (codeMat 157) (codeMat 486) true
    det491 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0185_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 71, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0185_orbit
  simpa only [lower144] using h

theorem space0186_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 64, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (64, 192), (35, 378), (19, 350), (10, 427)]
    (codeMat 303) (codeMat 185) (codeMat 481) false
    det303 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0186_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 64, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0186_orbit
  simpa only [lower220] using h

theorem space0187_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 71, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 495), (71, 493), (34, 463), (19, 441), (10, 462)]
    (codeMat 426) (codeMat 171) (codeMat 485) true
    det426 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0187_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 71, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0187_orbit
  simpa only [lower144] using h

theorem space0188_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 69, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (69, 34), (34, 440), (19, 462), (10, 441)]
    (codeMat 298) (codeMat 185) (codeMat 481) true
    det298 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0188_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 69, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0188_orbit
  simpa only [lower144] using h

theorem space0189_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [260, 66, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(260, 16), (66, 414), (33, 209), (19, 427), (10, 350)]
    (codeMat 431) (codeMat 171) (codeMat 485) false
    det431 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0189_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 66, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0189_orbit
  simpa only [lower220] using h

theorem space0190_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 71, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (71, 493), (32, 1), (19, 441), (10, 462)]
    (codeMat 482) (codeMat 143) (codeMat 482) true
    det482 det143 inv143
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0190_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 71, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0190_orbit
  simpa only [lower144] using h

theorem space0191_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 64, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (64, 192), (19, 350), (10, 245), (7, 36)]
    (codeMat 311) (codeMat 171) (codeMat 485) false
    det311 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0191_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 64, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0191_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
