import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0128_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(33, 20), (17, 21), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    det266 det394 inv394
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0128_lower : 15 ≤ frozenWangTable.L0 (spanCodes [33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0128_orbit
  simpa only [lower95] using h

theorem space0129_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    det266 det241 inv241
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0129_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0129_orbit
  simpa only [lower95] using h

theorem space0130_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(34, 52), (18, 54), (10, 53), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 465) (codeMat 465) false
    det266 det465 inv465
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0130_lower : 15 ≤ frozenWangTable.L0 (spanCodes [34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0130_orbit
  simpa only [lower95] using h

theorem space0131_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 9), (64, 8), (18, 54), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 282) (codeMat 267) true
    det84 det282 inv282
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0131_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0131_orbit
  simpa only [lower95] using h

theorem space0132_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [130, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(130, 63), (66, 60), (18, 54), (10, 52), (1, 32)]
    (codeMat 86) (codeMat 282) (codeMat 267) true
    det86 det282 inv282
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0132_lower : 15 ≤ frozenWangTable.L0 (spanCodes [130, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0132_orbit
  simpa only [lower95] using h

theorem space0133_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 8), (64, 1), (17, 20), (8, 2), (2, 32)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    det84 det273 inv273
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0133_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0133_orbit
  simpa only [lower95] using h

theorem space0134_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [129, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(129, 60), (65, 3), (17, 20), (8, 2), (2, 32)]
    (codeMat 87) (codeMat 273) (codeMat 273) true
    det87 det273 inv273
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0134_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0134_orbit
  simpa only [lower95] using h

theorem space0135_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [129, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(129, 35), (64, 63), (16, 2), (9, 54), (3, 32)]
    (codeMat 87) (codeMat 267) (codeMat 282) true
    det87 det267 inv267
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0135_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0135_orbit
  simpa only [lower95] using h

theorem space0136_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 3), (65, 63), (16, 2), (9, 54), (3, 32)]
    (codeMat 86) (codeMat 267) (codeMat 282) true
    det86 det267 inv267
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0136_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0136_orbit
  simpa only [lower95] using h

theorem space0137_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [129, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(129, 33), (65, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 85) (codeMat 267) (codeMat 282) true
    det85 det267 inv267
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0137_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0137_orbit
  simpa only [lower95] using h

theorem space0138_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 1), (64, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 84) (codeMat 267) (codeMat 282) true
    det84 det267 inv267
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0138_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0138_orbit
  simpa only [lower95] using h

theorem space0139_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 40), (65, 1), (17, 20), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    det85 det273 inv273
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0139_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0139_orbit
  simpa only [lower95] using h

theorem space0140_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [129, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(129, 28), (64, 3), (17, 20), (8, 2), (2, 32)]
    (codeMat 86) (codeMat 273) (codeMat 273) true
    det86 det273 inv273
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0140_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0140_orbit
  simpa only [lower95] using h

theorem space0141_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [128, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(128, 63), (66, 28), (18, 54), (10, 52), (1, 32)]
    (codeMat 87) (codeMat 282) (codeMat 267) true
    det87 det282 inv282
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0141_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0141_orbit
  simpa only [lower95] using h

theorem space0142_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [130, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(130, 9), (64, 40), (18, 54), (10, 52), (1, 32)]
    (codeMat 85) (codeMat 282) (codeMat 267) true
    det85 det282 inv282
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0142_lower : 15 ≤ frozenWangTable.L0 (spanCodes [130, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0142_orbit
  simpa only [lower95] using h

theorem space0143_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [257, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(257, 112), (32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    det266 det92 inv92
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0143_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0143_orbit
  simpa only [lower31] using h

theorem space0144_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [257, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(257, 80), (32, 1), (17, 20), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0144_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0144_orbit
  simpa only [lower31] using h

theorem space0145_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 112), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    det266 det212 inv212
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0145_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0145_orbit
  simpa only [lower31] using h

theorem space0146_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 96, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (96, 34), (19, 462), (10, 119), (4, 1)]
    (codeMat 305) (codeMat 143) (codeMat 482) true
    det305 det143 inv143
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0146_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 96, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0146_orbit
  simpa only [lower144] using h

theorem space0147_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [289, 97, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(289, 33), (97, 35), (19, 441), (10, 119), (5, 1)]
    (codeMat 481) (codeMat 185) (codeMat 481) true
    det481 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0147_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 97, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0147_orbit
  simpa only [lower144] using h

theorem space0148_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 96, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (96, 34), (19, 462), (10, 119), (5, 1)]
    (codeMat 417) (codeMat 171) (codeMat 485) true
    det417 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0148_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 96, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0148_orbit
  simpa only [lower144] using h

theorem space0149_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 97, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (97, 35), (19, 441), (10, 119), (4, 1)]
    (codeMat 369) (codeMat 157) (codeMat 486) true
    det369 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0149_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 97, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0149_orbit
  simpa only [lower144] using h

theorem space0150_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 66, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (66, 53), (19, 350), (10, 245), (7, 36)]
    (codeMat 421) (codeMat 171) (codeMat 485) false
    det421 det171 inv171
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0150_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 66, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0150_orbit
  simpa only [lower220] using h

theorem space0151_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [256, 67, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(256, 16), (67, 53), (19, 427), (10, 245), (6, 36)]
    (codeMat 485) (codeMat 185) (codeMat 481) false
    det485 det185 inv185
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0151_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 67, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0151_orbit
  simpa only [lower220] using h

theorem space0152_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 66, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 37), (66, 53), (19, 350), (10, 245), (6, 36)]
    (codeMat 421) (codeMat 143) (codeMat 482) false
    det421 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0152_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 66, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0152_orbit
  simpa only [lower220] using h

theorem space0153_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 67, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 37), (67, 53), (19, 427), (10, 245), (7, 36)]
    (codeMat 485) (codeMat 157) (codeMat 486) false
    det485 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0153_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 67, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space0153_orbit
  simpa only [lower220] using h

theorem space0154_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 68, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (68, 34), (32, 1), (19, 462), (10, 441)]
    (codeMat 298) (codeMat 157) (codeMat 486) true
    det298 det157 inv157
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0154_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 68, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0154_orbit
  simpa only [lower144] using h

theorem space0155_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [261, 64, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(261, 208), (64, 192), (37, 209), (19, 245), (10, 427)]
    (codeMat 302) (codeMat 143) (codeMat 482) false
    det302 det143 inv143
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0155_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 64, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0155_orbit
  simpa only [lower220] using h

theorem space0156_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 65, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 208), (65, 192), (33, 209), (19, 350), (10, 427)]
    (codeMat 358) (codeMat 157) (codeMat 486) false
    det358 det157 inv157
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0156_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 65, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0156_orbit
  simpa only [lower220] using h

theorem space0157_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 69, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (69, 34), (36, 1), (19, 119), (10, 441)]
    (codeMat 355) (codeMat 143) (codeMat 482) true
    det355 det143 inv143
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0157_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 69, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0157_orbit
  simpa only [lower144] using h

theorem space0158_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [262, 70, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(262, 495), (70, 493), (34, 463), (19, 441), (10, 462)]
    (codeMat 482) (codeMat 171) (codeMat 485) true
    det482 det171 inv171
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0158_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 70, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0158_orbit
  simpa only [lower144] using h

theorem space0159_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 68, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (68, 34), (34, 440), (19, 462), (10, 441)]
    (codeMat 354) (codeMat 185) (codeMat 481) true
    det354 det185 inv185
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0159_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 68, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0159_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
