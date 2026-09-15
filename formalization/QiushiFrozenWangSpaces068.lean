import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2176_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 129, 68, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 224), (129, 227), (68, 255), (39, 96), (17, 97), (10, 105)]
    (codeMat 115) (codeMat 459) (codeMat 346) true
    det115 det459 inv459
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2176_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 68, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2176_orbit
  simpa only [lower35] using h

theorem space2177_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [257, 135, 68, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(257, 68), (135, 71), (68, 69), (39, 160), (17, 184), (10, 168)]
    (codeMat 93) (codeMat 467) (codeMat 339) false
    det93 det467 inv467
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2177_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2177_orbit
  simpa only [lower29] using h

theorem space2178_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 134, 68, 32, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (134, 139), (68, 126), (32, 8), (22, 136), (10, 232)]
    (codeMat 214) (codeMat 94) (codeMat 500) false
    det214 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2178_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 68, 32, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2178_orbit
  simpa only [lower35] using h

theorem space2179_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (128, 9), (68, 104), (38, 28), (22, 31), (10, 252)]
    (codeMat 116) (codeMat 122) (codeMat 460) true
    det116 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2179_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2179_orbit
  simpa only [lower35] using h

theorem space2180_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 129, 68, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 126), (129, 252), (68, 119), (39, 232), (23, 104), (10, 224)]
    (codeMat 158) (codeMat 489) (codeMat 241) false
    det158 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2180_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2180_orbit
  simpa only [lower35] using h

theorem space2181_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 131, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 31), (131, 224), (68, 252), (36, 9), (17, 96), (10, 104)]
    (codeMat 123) (codeMat 236) (codeMat 123) true
    det123 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2181_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 131, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2181_orbit
  simpa only [lower35] using h

theorem space2182_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [256, 132, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    det92 det204 inv204
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2182_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2182_orbit
  simpa only [lower29] using h

theorem space2183_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 135, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 136), (135, 104), (68, 232), (36, 3), (17, 148), (10, 150)]
    (codeMat 355) (codeMat 236) (codeMat 123) false
    det355 det236 inv236
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2183_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2183_orbit
  simpa only [lower35] using h

theorem space2184_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 132, 68, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 31), (132, 252), (68, 255), (39, 22), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 253) (codeMat 415) true
    det95 det253 inv253
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2184_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 68, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2184_orbit
  simpa only [lower35] using h

theorem space2185_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 224), (130, 3), (68, 255), (32, 128), (16, 2), (10, 150)]
    (codeMat 87) (codeMat 331) (codeMat 410) true
    det87 det331 inv331
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2185_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2185_orbit
  simpa only [lower35] using h

theorem space2186_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    det298 det345 inv345
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2186_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2186_orbit
  simpa only [lower35] using h

theorem space2187_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [257, 130, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(257, 68), (130, 2), (68, 69), (34, 160), (16, 16), (10, 168)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    det85 det337 inv337
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2187_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2187_orbit
  simpa only [lower29] using h

theorem space2188_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 68, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (135, 22), (68, 150), (34, 252), (21, 31), (10, 255)]
    (codeMat 111) (codeMat 379) (codeMat 247) true
    det111 det379 inv379
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2188_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2188_orbit
  simpa only [lower35] using h

theorem space2189_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 68, 35, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (132, 96), (68, 105), (35, 28), (22, 224), (10, 255)]
    (codeMat 124) (codeMat 233) (codeMat 233) true
    det124 det233 inv233
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2189_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 35, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2189_orbit
  simpa only [lower35] using h

theorem space2190_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 68, 36, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (131, 252), (68, 119), (36, 8), (22, 104), (10, 224)]
    (codeMat 159) (codeMat 205) (codeMat 242) false
    det159 det205 inv205
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2190_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 68, 36, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2190_orbit
  simpa only [lower35] using h

theorem space2191_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 130, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (130, 128), (68, 104), (32, 1), (16, 2), (10, 148)]
    (codeMat 354) (codeMat 84) (codeMat 84) false
    det354 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2191_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2191_orbit
  simpa only [lower35] using h

theorem space2192_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 135, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 8), (135, 232), (68, 104), (36, 1), (17, 150), (10, 148)]
    (codeMat 355) (codeMat 212) (codeMat 86) false
    det355 det212 inv212
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2192_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2192_orbit
  simpa only [lower35] using h

theorem space2193_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 104), (128, 128), (68, 96), (34, 148), (16, 2), (10, 149)]
    (codeMat 298) (codeMat 337) (codeMat 337) false
    det298 det337 inv337
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2193_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2193_orbit
  simpa only [lower35] using h

theorem space2194_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 130, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 96), (130, 1), (68, 104), (32, 128), (16, 2), (10, 148)]
    (codeMat 85) (codeMat 330) (codeMat 394) true
    det85 det330 inv330
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2194_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2194_orbit
  simpa only [lower35] using h

theorem space2195_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (132, 20), (68, 148), (32, 1), (16, 8), (10, 104)]
    (codeMat 98) (codeMat 92) (codeMat 116) true
    det98 det92 inv92
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2195_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2195_orbit
  simpa only [lower35] using h

theorem space2196_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (135, 20), (68, 150), (34, 104), (16, 8), (10, 105)]
    (codeMat 106) (codeMat 377) (codeMat 369) true
    det106 det377 inv377
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2196_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2196_orbit
  simpa only [lower35] using h

theorem space2197_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 128), (68, 148), (36, 1), (17, 96), (10, 104)]
    (codeMat 99) (codeMat 204) (codeMat 114) true
    det99 det204 inv204
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2197_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2197_orbit
  simpa only [lower35] using h

theorem space2198_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 68, 34, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 150), (135, 149), (68, 148), (34, 232), (17, 96), (10, 104)]
    (codeMat 157) (codeMat 482) (codeMat 143) false
    det157 det482 inv482
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2198_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 34, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2198_orbit
  simpa only [lower35] using h

theorem space2199_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [290, 144, 66, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(290, 22), (144, 2), (66, 81), (10, 80), (6, 32), (1, 8)]
    (codeMat 142) (codeMat 305) (codeMat 305) false
    det142 det305 inv305
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2199_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 144, 66, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2199_orbit
  simpa only [lower31] using h

theorem space2200_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [288, 146, 66, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(288, 2), (146, 54), (66, 113), (10, 112), (6, 32), (1, 8)]
    (codeMat 142) (codeMat 177) (codeMat 417) false
    det142 det177 inv177
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2200_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 146, 66, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2200_orbit
  simpa only [lower31] using h

theorem space2201_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [386, 66, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(386, 88), (66, 90), (48, 32), (10, 108), (6, 8), (1, 9)]
    (codeMat 161) (codeMat 409) (codeMat 473) true
    det161 det409 inv409
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2201_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 66, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2201_orbit
  simpa only [lower31] using h

theorem space2202_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [384, 66, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(384, 2), (66, 83), (50, 69), (10, 101), (6, 1), (1, 9)]
    (codeMat 161) (codeMat 395) (codeMat 474) true
    det161 det395 inv395
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2202_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 66, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2202_orbit
  simpa only [lower31] using h

theorem space2203_orbit :
    frozenWangTable.OrbitImage 141 (spanCodes [279, 144, 68, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 141 [(279, 299), (144, 2), (68, 350), (49, 265), (10, 383)]
    (codeMat 254) (codeMat 369) (codeMat 377) false
    det254 det369 inv369
    (by rw [basis141]; decide +kernel)
    (by rw [basis141]; decide +kernel)

theorem space2203_lower : 15 ≤ frozenWangTable.L0 (spanCodes [279, 144, 68, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 141 space2203_orbit
  simpa only [lower141] using h

theorem space2204_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [290, 146, 66, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(290, 41), (146, 40), (66, 175), (10, 173), (6, 9)]
    (codeMat 190) (codeMat 394) (codeMat 330) false
    det190 det394 inv394
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2204_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 146, 66, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 103 space2204_orbit
  simpa only [lower103] using h

theorem space2205_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [291, 147, 66, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(291, 43), (147, 42), (66, 175), (10, 173), (6, 9)]
    (codeMat 254) (codeMat 442) (codeMat 334) false
    det254 det442 inv442
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2205_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 147, 66, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 103 space2205_orbit
  simpa only [lower103] using h

theorem space2206_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [386, 66, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(386, 135), (66, 175), (50, 134), (10, 166), (6, 2)]
    (codeMat 142) (codeMat 395) (codeMat 474) true
    det142 det395 inv395
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2206_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 66, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 103 space2206_orbit
  simpa only [lower103] using h

theorem space2207_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [289, 144, 67, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(289, 34), (144, 40), (67, 175), (10, 173), (7, 9)]
    (codeMat 183) (codeMat 426) (codeMat 335) false
    det183 det426 inv426
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2207_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 144, 67, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space2207_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
