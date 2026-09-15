import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0096_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [320, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(320, 1), (19, 304), (10, 400)]
    (codeMat 84) (codeMat 188) (codeMat 103) false
    det84 det188 inv188
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0096_lower : 17 ≤ frozenWangTable.L0 (spanCodes [320, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0096_orbit
  simpa only [lower446] using h

theorem space0097_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [262, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(262, 21), (70, 20), (19, 472), (10, 312)]
    (codeMat 140) (codeMat 470) (codeMat 213) false
    det140 det470 inv470
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space0097_lower : 17 ≤ frozenWangTable.L0 (spanCodes [262, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space0097_orbit
  simpa only [lower373] using h

theorem space0098_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [354, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(354, 401), (19, 304), (10, 400)]
    (codeMat 86) (codeMat 188) (codeMat 103) false
    det86 det188 inv188
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0098_lower : 17 ≤ frozenWangTable.L0 (spanCodes [354, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0098_orbit
  simpa only [lower446] using h

theorem space0099_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [257, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(257, 301), (99, 460), (19, 472), (10, 224)]
    (codeMat 86) (codeMat 342) (codeMat 215) false
    det86 det342 inv342
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space0099_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space0099_orbit
  simpa only [lower373] using h

theorem space0100_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [261, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(261, 301), (103, 460), (19, 312), (10, 224)]
    (codeMat 94) (codeMat 470) (codeMat 213) false
    det94 det470 inv470
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space0100_lower : 17 ≤ frozenWangTable.L0 (spanCodes [261, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space0100_orbit
  simpa only [lower373] using h

theorem space0101_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [359, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(359, 401), (19, 304), (10, 400)]
    (codeMat 87) (codeMat 188) (codeMat 103) false
    det87 det188 inv188
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0101_lower : 17 ≤ frozenWangTable.L0 (spanCodes [359, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0101_orbit
  simpa only [lower446] using h

theorem space0102_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [384, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(384, 1), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    det84 det116 inv116
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0102_lower : 17 ≤ frozenWangTable.L0 (spanCodes [384, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0102_orbit
  simpa only [lower446] using h

theorem space0103_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [390, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(390, 1), (19, 400), (10, 160)]
    (codeMat 85) (codeMat 116) (codeMat 92) false
    det85 det116 inv116
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0103_lower : 17 ≤ frozenWangTable.L0 (spanCodes [390, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0103_orbit
  simpa only [lower446] using h

theorem space0104_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [257, 162, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(257, 245), (162, 300), (19, 472), (10, 312)]
    (codeMat 214) (codeMat 397) (codeMat 250) false
    det214 det397 inv397
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space0104_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 162, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space0104_orbit
  simpa only [lower373] using h

theorem space0105_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [448, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(448, 1), (19, 160), (10, 304)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    det84 det236 inv236
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0105_lower : 17 ≤ frozenWangTable.L0 (spanCodes [448, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0105_orbit
  simpa only [lower446] using h

theorem space0106_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [455, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(455, 1), (19, 160), (10, 304)]
    (codeMat 85) (codeMat 236) (codeMat 123) false
    det85 det236 inv236
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0106_lower : 17 ≤ frozenWangTable.L0 (spanCodes [455, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0106_orbit
  simpa only [lower446] using h

theorem space0107_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [484, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(484, 265), (18, 27), (10, 26), (1, 16)]
    (codeMat 458) (codeMat 286) (codeMat 303) false
    det458 det286 inv286
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space0107_lower : 17 ≤ frozenWangTable.L0 (spanCodes [484, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 282 space0107_orbit
  simpa only [lower282] using h

theorem space0108_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [256, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(256, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    det266 det282 inv282
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0108_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0108_orbit
  simpa only [lower281] using h

theorem space0109_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [256, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(256, 256), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0109_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 281 space0109_orbit
  simpa only [lower281] using h

theorem space0110_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [260, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(260, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 330) (codeMat 282) (codeMat 267) false
    det330 det282 inv282
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0110_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0110_orbit
  simpa only [lower281] using h

theorem space0111_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [288, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(288, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 394) (codeMat 282) (codeMat 267) false
    det394 det282 inv282
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0111_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0111_orbit
  simpa only [lower281] using h

theorem space0112_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [288, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(288, 256), (17, 10), (8, 1), (2, 16)]
    (codeMat 394) (codeMat 273) (codeMat 273) false
    det394 det273 inv273
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0112_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 281 space0112_orbit
  simpa only [lower281] using h

theorem space0113_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [292, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(292, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 458) (codeMat 282) (codeMat 267) false
    det458 det282 inv282
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0113_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0113_orbit
  simpa only [lower281] using h

theorem space0114_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [324, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(324, 272), (18, 27), (10, 26), (1, 16)]
    (codeMat 330) (codeMat 314) (codeMat 271) false
    det330 det314 inv314
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0114_lower : 16 ≤ frozenWangTable.L0 (spanCodes [324, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0114_orbit
  simpa only [lower281] using h

theorem space0115_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [358, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(358, 266), (18, 27), (10, 26), (1, 16)]
    (codeMat 458) (codeMat 314) (codeMat 271) false
    det458 det314 inv314
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0115_lower : 16 ≤ frozenWangTable.L0 (spanCodes [358, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0115_orbit
  simpa only [lower281] using h

theorem space0116_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [384, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(384, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 318) (codeMat 299) false
    det266 det318 inv318
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0116_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0116_orbit
  simpa only [lower281] using h

theorem space0117_orbit :
    frozenWangTable.OrbitImage 281 (spanCodes [480, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 281 [(480, 257), (18, 27), (10, 26), (1, 16)]
    (codeMat 394) (codeMat 286) (codeMat 303) false
    det394 det286 inv286
    (by rw [basis281]; decide +kernel)
    (by rw [basis281]; decide +kernel)

theorem space0117_lower : 16 ≤ frozenWangTable.L0 (spanCodes [480, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 281 space0117_orbit
  simpa only [lower281] using h

theorem space0118_orbit :
    frozenWangTable.OrbitImage 250 (spanCodes [16, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 250 [(16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis250]; decide +kernel)
    (by rw [basis250]; decide +kernel)

theorem space0118_lower : 15 ≤ frozenWangTable.L0 (spanCodes [16, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 250 space0118_orbit
  simpa only [lower250] using h

theorem space0119_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    det266 det212 inv212
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0119_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0119_orbit
  simpa only [lower95] using h

theorem space0120_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    det266 det498 inv498
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0120_lower : 15 ≤ frozenWangTable.L0 (spanCodes [34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 95 space0120_orbit
  simpa only [lower95] using h

theorem space0121_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 1), (17, 20), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0121_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0121_orbit
  simpa only [lower95] using h

theorem space0122_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(33, 30), (17, 28), (8, 3), (5, 40), (2, 32)]
    (codeMat 266) (codeMat 425) (codeMat 249) false
    det266 det425 inv425
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0122_lower : 15 ≤ frozenWangTable.L0 (spanCodes [33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0122_orbit
  simpa only [lower95] using h

theorem space0123_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(33, 60), (16, 2), (9, 63), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 345) (codeMat 345) false
    det266 det345 inv345
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0123_lower : 15 ≤ frozenWangTable.L0 (spanCodes [33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0123_orbit
  simpa only [lower95] using h

theorem space0124_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 2), (16, 3), (9, 54), (5, 32), (3, 40)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    det266 det122 inv122
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0124_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0124_orbit
  simpa only [lower95] using h

theorem space0125_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(33, 62), (16, 2), (9, 63), (5, 8), (3, 40)]
    (codeMat 266) (codeMat 377) (codeMat 369) false
    det266 det377 inv377
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0125_lower : 15 ≤ frozenWangTable.L0 (spanCodes [33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0125_orbit
  simpa only [lower95] using h

theorem space0126_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    det266 det92 inv92
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0126_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 95 space0126_orbit
  simpa only [lower95] using h

theorem space0127_orbit :
    frozenWangTable.OrbitImage 95 (spanCodes [32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 95 [(32, 2), (17, 28), (8, 3), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 169) (codeMat 225) false
    det266 det169 inv169
    (by rw [basis95]; decide +kernel)
    (by rw [basis95]; decide +kernel)

theorem space0127_lower : 15 ≤ frozenWangTable.L0 (spanCodes [32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 95 space0127_orbit
  simpa only [lower95] using h


end QiushiMatmul.FrozenWang
