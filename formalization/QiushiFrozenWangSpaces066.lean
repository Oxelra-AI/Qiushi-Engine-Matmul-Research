import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2112_orbit :
    frozenWangTable.OrbitImage 428 (spanCodes [68, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 428 [(68, 96), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    det267 det275 inv275
    (by rw [basis428]; decide +kernel)
    (by rw [basis428]; decide +kernel)

theorem space2112_lower : 17 ≤ frozenWangTable.L0 (spanCodes [68, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 428 space2112_orbit
  simpa only [lower428] using h

theorem space2113_orbit :
    frozenWangTable.OrbitImage 428 (spanCodes [65, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 428 [(65, 1), (10, 96), (5, 16)]
    (codeMat 141) (codeMat 165) (codeMat 163) false
    det141 det165 inv165
    (by rw [basis428]; decide +kernel)
    (by rw [basis428]; decide +kernel)

theorem space2113_lower : 17 ≤ frozenWangTable.L0 (spanCodes [65, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 428 space2113_orbit
  simpa only [lower428] using h

theorem space2114_orbit :
    frozenWangTable.OrbitImage 428 (spanCodes [66, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 428 [(66, 113), (10, 112), (6, 16)]
    (codeMat 142) (codeMat 401) (codeMat 401) false
    det142 det401 inv401
    (by rw [basis428]; decide +kernel)
    (by rw [basis428]; decide +kernel)

theorem space2114_lower : 17 ≤ frozenWangTable.L0 (spanCodes [66, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 428 space2114_orbit
  simpa only [lower428] using h

theorem space2115_orbit :
    frozenWangTable.OrbitImage 428 (spanCodes [67, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 428 [(67, 113), (10, 112), (7, 16)]
    (codeMat 143) (codeMat 405) (codeMat 407) false
    det143 det405 inv405
    (by rw [basis428]; decide +kernel)
    (by rw [basis428]; decide +kernel)

theorem space2115_lower : 17 ≤ frozenWangTable.L0 (spanCodes [67, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 428 space2115_orbit
  simpa only [lower428] using h

theorem space2116_orbit :
    frozenWangTable.OrbitImage 431 (spanCodes [68, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 431 [(68, 228), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 267) (codeMat 282) false
    det275 det267 inv267
    (by rw [basis431]; decide +kernel)
    (by rw [basis431]; decide +kernel)

theorem space2116_lower : 17 ≤ frozenWangTable.L0 (spanCodes [68, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 431 space2116_orbit
  simpa only [lower431] using h

theorem space2117_orbit :
    frozenWangTable.OrbitImage 431 (spanCodes [260, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 431 [(260, 1), (68, 17), (10, 228)]
    (codeMat 165) (codeMat 141) (codeMat 226) false
    det165 det141 inv141
    (by rw [basis431]; decide +kernel)
    (by rw [basis431]; decide +kernel)

theorem space2117_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 431 space2117_orbit
  simpa only [lower431] using h

theorem space2118_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [257, 68, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(257, 11), (68, 10), (50, 430), (10, 170)]
    (codeMat 461) (codeMat 174) (codeMat 359) false
    det461 det174 inv174
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2118_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 68, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2118_orbit
  simpa only [lower315] using h

theorem space2119_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [291, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(291, 430), (68, 160), (16, 1), (10, 10)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    det330 det298 inv298
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2119_lower : 17 ≤ frozenWangTable.L0 (spanCodes [291, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2119_orbit
  simpa only [lower315] using h

theorem space2120_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 68, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 1), (68, 10), (53, 430), (10, 170)]
    (codeMat 460) (codeMat 158) (codeMat 358) false
    det460 det158 inv158
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2120_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 68, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2120_orbit
  simpa only [lower315] using h

theorem space2121_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 144, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 1), (144, 260), (68, 10), (10, 160)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    det140 det140 inv140
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2121_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 144, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2121_orbit
  simpa only [lower315] using h

theorem space2122_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [384, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(384, 260), (68, 170), (16, 1), (10, 10)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    det394 det270 inv270
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2122_lower : 17 ≤ frozenWangTable.L0 (spanCodes [384, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2122_orbit
  simpa only [lower315] using h

theorem space2123_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [257, 146, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(257, 11), (146, 260), (68, 10), (10, 160)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    det141 det172 inv172
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2123_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 146, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2123_orbit
  simpa only [lower315] using h

theorem space2124_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [387, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(387, 430), (68, 170), (16, 1), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    det458 det302 inv302
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2124_lower : 17 ≤ frozenWangTable.L0 (spanCodes [387, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2124_orbit
  simpa only [lower315] using h

theorem space2125_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [388, 68, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(388, 430), (68, 170), (17, 11), (10, 10)]
    (codeMat 459) (codeMat 286) (codeMat 303) false
    det459 det286 inv286
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2125_lower : 17 ≤ frozenWangTable.L0 (spanCodes [388, 68, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2125_orbit
  simpa only [lower315] using h

theorem space2126_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [390, 68, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(390, 260), (68, 170), (17, 11), (10, 10)]
    (codeMat 395) (codeMat 318) (codeMat 299) false
    det395 det318 inv318
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2126_lower : 17 ≤ frozenWangTable.L0 (spanCodes [390, 68, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2126_orbit
  simpa only [lower315] using h

theorem space2127_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [304, 128, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(304, 261), (128, 260), (68, 170), (10, 160)]
    (codeMat 142) (codeMat 396) (codeMat 106) false
    det142 det396 inv396
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2127_lower : 17 ≤ frozenWangTable.L0 (spanCodes [304, 128, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2127_orbit
  simpa only [lower315] using h

theorem space2128_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [311, 135, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(311, 431), (135, 430), (68, 170), (10, 160)]
    (codeMat 206) (codeMat 444) (codeMat 110) false
    det206 det444 inv444
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2128_lower : 17 ≤ frozenWangTable.L0 (spanCodes [311, 135, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2128_orbit
  simpa only [lower315] using h

theorem space2129_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [403, 68, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(403, 421), (68, 160), (34, 430), (10, 170)]
    (codeMat 335) (codeMat 426) (codeMat 335) false
    det335 det426 inv426
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2129_lower : 17 ≤ frozenWangTable.L0 (spanCodes [403, 68, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2129_orbit
  simpa only [lower315] using h

theorem space2130_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [405, 68, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(405, 271), (68, 160), (36, 260), (10, 170)]
    (codeMat 271) (codeMat 410) (codeMat 331) false
    det271 det410 inv410
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2130_lower : 17 ≤ frozenWangTable.L0 (spanCodes [405, 68, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2130_orbit
  simpa only [lower315] using h

theorem space2131_orbit :
    frozenWangTable.OrbitImage 431 (spanCodes [438, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 431 [(438, 1), (68, 245), (10, 228)]
    (codeMat 183) (codeMat 397) (codeMat 250) false
    det183 det397 inv397
    (by rw [basis431]; decide +kernel)
    (by rw [basis431]; decide +kernel)

theorem space2131_lower : 17 ≤ frozenWangTable.L0 (spanCodes [438, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 431 space2131_orbit
  simpa only [lower431] using h

theorem space2132_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [272, 144, 68, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(272, 26), (144, 1), (68, 164), (32, 16), (10, 96)]
    (codeMat 86) (codeMat 98) (codeMat 140) false
    det86 det98 inv98
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2132_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 144, 68, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2132_orbit
  simpa only [lower152] using h

theorem space2133_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [273, 149, 68, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(273, 122), (149, 197), (68, 164), (36, 16), (10, 96)]
    (codeMat 95) (codeMat 226) (codeMat 141) false
    det95 det226 inv226
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2133_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 149, 68, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2133_orbit
  simpa only [lower152] using h

theorem space2134_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [273, 132, 68, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(273, 107), (132, 197), (68, 196), (53, 112), (10, 96)]
    (codeMat 92) (codeMat 230) (codeMat 159) false
    det92 det230 inv230
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2134_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 132, 68, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2134_orbit
  simpa only [lower152] using h

theorem space2135_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [272, 150, 68, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(272, 222), (150, 197), (68, 164), (39, 112), (10, 96)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    det94 det482 inv482
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2135_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 150, 68, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2135_orbit
  simpa only [lower152] using h

theorem space2136_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [272, 135, 68, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(272, 175), (135, 197), (68, 196), (54, 16), (10, 96)]
    (codeMat 93) (codeMat 486) (codeMat 157) false
    det93 det486 inv486
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2136_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 135, 68, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2136_orbit
  simpa only [lower152] using h

theorem space2137_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [257, 144, 68, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(257, 78), (144, 27), (68, 79), (53, 264), (10, 280)]
    (codeMat 157) (codeMat 379) (codeMat 247) false
    det157 det379 inv379
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2137_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 144, 68, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2137_orbit
  simpa only [lower150] using h

theorem space2138_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [68, 32, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(68, 164), (32, 32), (17, 10), (9, 2), (3, 9)]
    (codeMat 275) (codeMat 282) (codeMat 267) false
    det275 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2138_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 32, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2138_orbit
  simpa only [lower103] using h

theorem space2139_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [68, 33, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(68, 164), (33, 34), (17, 10), (9, 2), (3, 9)]
    (codeMat 339) (codeMat 314) (codeMat 271) false
    det339 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2139_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 33, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2139_orbit
  simpa only [lower103] using h

theorem space2140_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [68, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(68, 112), (36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    det266 det417 inv417
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2140_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2140_orbit
  simpa only [lower31] using h

theorem space2141_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [68, 36, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(68, 164), (36, 32), (16, 1), (8, 2), (2, 9)]
    (codeMat 282) (codeMat 266) (codeMat 266) false
    det282 det266 inv266
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2141_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 36, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2141_orbit
  simpa only [lower103] using h

theorem space2142_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 68, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 32), (68, 164), (17, 10), (9, 9), (3, 2)]
    (codeMat 267) (codeMat 281) (codeMat 281) true
    det267 det281 inv281
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2142_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 68, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2142_orbit
  simpa only [lower103] using h

theorem space2143_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [129, 68, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(129, 34), (68, 166), (17, 10), (9, 9), (3, 2)]
    (codeMat 331) (codeMat 313) (codeMat 313) true
    det331 det313 inv313
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2143_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 68, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2143_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
