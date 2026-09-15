import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2240_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 129, 65, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (129, 326), (65, 325), (32, 8), (18, 432), (10, 424), (5, 256)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    det84 det213 inv213
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2240_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space2240_orbit
  simpa only [lower10] using h

theorem space2241_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 65, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 3), (65, 325), (33, 264), (18, 24), (10, 424), (5, 256)]
    (codeMat 92) (codeMat 87) (codeMat 468) false
    det92 det87 inv87
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2241_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space2241_orbit
  simpa only [lower10] using h

theorem space2242_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 65, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 240), (130, 8), (65, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    det106 det354 inv354
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2242_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space2242_orbit
  simpa only [lower11] using h

theorem space2243_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 68, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2243_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2243_orbit
  simpa only [lower11] using h

theorem space2244_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 68, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 68), (128, 130), (68, 69), (32, 32), (21, 80), (8, 40), (2, 128)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    det85 det337 inv337
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2244_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 68, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space2244_orbit
  simpa only [lower11] using h

theorem space2245_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 132, 68, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 68), (132, 199), (68, 69), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 93) (codeMat 467) (codeMat 339) false
    det93 det467 inv467
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2245_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2245_orbit
  simpa only [lower11] using h

theorem space2246_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 132, 68, 36, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 1), (132, 70), (68, 68), (36, 8), (21, 240), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 212) (codeMat 86) false
    det92 det212 inv212
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2246_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 36, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space2246_orbit
  simpa only [lower11] using h

theorem space2247_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 67, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 258), (130, 1), (67, 71), (35, 272), (18, 8), (10, 440), (7, 256)]
    (codeMat 93) (codeMat 107) (codeMat 428) false
    det93 det107 inv107
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2247_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2247_orbit
  simpa only [lower10] using h

theorem space2248_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 131, 67, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 69), (131, 70), (67, 71), (34, 424), (18, 432), (10, 440), (7, 256)]
    (codeMat 84) (codeMat 477) (codeMat 431) false
    det84 det477 inv477
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2248_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space2248_orbit
  simpa only [lower10] using h

theorem space2249_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 128, 66, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 68), (128, 325), (66, 170), (32, 256), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    det142 det394 inv394
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2249_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 128, 66, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2249_orbit
  simpa only [lower10] using h

theorem space2250_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 33, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 198), (129, 199), (64, 3), (33, 240), (17, 248), (9, 216), (4, 384), (3, 256)]
    (codeMat 84) (codeMat 443) (codeMat 254) false
    det84 det443 inv443
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2250_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2250_orbit
  simpa only [lower3] using h

theorem space2251_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (129, 324), (65, 325), (33, 344), (16, 32), (8, 40), (5, 384), (2, 256)]
    (codeMat 84) (codeMat 229) (codeMat 187) false
    det84 det229 inv229
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2251_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space2251_orbit
  simpa only [lower3] using h

theorem space2252_orbit :
    frozenWangTable.OrbitImage 1 (spanCodes [256, 128, 64, 32, 8, 4, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 1 [(256, 1), (128, 4), (64, 2), (32, 64), (8, 128), (4, 8), (2, 32), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    det140 det140 inv140
    (by rw [basis1]; decide +kernel)
    (by rw [basis1]; decide +kernel)

theorem space2252_lower : 3 ≤ frozenWangTable.L0 (spanCodes [256, 128, 64, 32, 8, 4, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 1 space2252_orbit
  simpa only [lower1] using h

theorem space2253_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 161), (33, 20), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2253_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2253_orbit
  simpa only [lower456] using h

theorem space2254_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 35, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 161), (35, 30), (10, 10)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    det330 det298 inv298
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2254_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 35, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2254_orbit
  simpa only [lower456] using h

theorem space2255_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 37, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 171), (37, 20), (10, 10)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    det331 det282 inv282
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2255_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 37, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2255_orbit
  simpa only [lower456] using h

theorem space2256_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 38, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 171), (38, 30), (10, 10)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    det267 det314 inv314
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2256_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 38, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2256_orbit
  simpa only [lower456] using h

theorem space2257_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 171), (49, 20), (10, 10)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    det394 det270 inv270
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2257_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2257_orbit
  simpa only [lower456] using h

theorem space2258_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 171), (51, 30), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    det458 det302 inv302
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2258_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2258_orbit
  simpa only [lower456] using h

theorem space2259_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 52, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 161), (52, 30), (10, 10)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    det395 det286 inv286
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2259_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 52, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2259_orbit
  simpa only [lower456] using h

theorem space2260_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [84, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(84, 161), (55, 20), (10, 10)]
    (codeMat 459) (codeMat 318) (codeMat 299) false
    det459 det318 inv318
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2260_lower : 18 ≤ frozenWangTable.L0 (spanCodes [84, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2260_orbit
  simpa only [lower456] using h

theorem space2261_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [129, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(129, 10), (84, 161), (10, 20)]
    (codeMat 140) (codeMat 273) (codeMat 273) true
    det140 det273 inv273
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2261_lower : 18 ≤ frozenWangTable.L0 (spanCodes [129, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2261_orbit
  simpa only [lower456] using h

theorem space2262_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [131, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(131, 10), (84, 161), (10, 20)]
    (codeMat 141) (codeMat 277) (codeMat 277) true
    det141 det277 inv277
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2262_lower : 18 ≤ frozenWangTable.L0 (spanCodes [131, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2262_orbit
  simpa only [lower456] using h

theorem space2263_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [132, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(132, 191), (84, 161), (10, 20)]
    (codeMat 207) (codeMat 311) (codeMat 307) true
    det207 det311 inv311
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2263_lower : 18 ≤ frozenWangTable.L0 (spanCodes [132, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2263_orbit
  simpa only [lower456] using h

theorem space2264_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [135, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(135, 191), (84, 161), (10, 20)]
    (codeMat 206) (codeMat 307) (codeMat 311) true
    det206 det307 inv307
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2264_lower : 18 ≤ frozenWangTable.L0 (spanCodes [135, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2264_orbit
  simpa only [lower456] using h

theorem space2265_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [145, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(145, 10), (84, 181), (10, 20)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    det142 det305 inv305
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2265_lower : 18 ≤ frozenWangTable.L0 (spanCodes [145, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2265_orbit
  simpa only [lower456] using h

theorem space2266_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [147, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(147, 10), (84, 181), (10, 20)]
    (codeMat 143) (codeMat 309) (codeMat 309) true
    det143 det309 inv309
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2266_lower : 18 ≤ frozenWangTable.L0 (spanCodes [147, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2266_orbit
  simpa only [lower456] using h

theorem space2267_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [149, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(149, 191), (84, 181), (10, 20)]
    (codeMat 204) (codeMat 279) (codeMat 279) true
    det204 det279 inv279
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2267_lower : 18 ≤ frozenWangTable.L0 (spanCodes [149, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2267_orbit
  simpa only [lower456] using h

theorem space2268_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [150, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(150, 191), (84, 181), (10, 20)]
    (codeMat 205) (codeMat 275) (codeMat 275) true
    det205 det275 inv275
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2268_lower : 18 ≤ frozenWangTable.L0 (spanCodes [150, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2268_orbit
  simpa only [lower456] using h

theorem space2269_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [161, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(161, 253), (84, 179), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    det267 det286 inv286
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space2269_lower : 18 ≤ frozenWangTable.L0 (spanCodes [161, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space2269_orbit
  simpa only [lower463] using h

theorem space2270_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [162, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(162, 162), (84, 230), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    det275 det313 inv313
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2270_lower : 18 ≤ frozenWangTable.L0 (spanCodes [162, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2270_orbit
  simpa only [lower461] using h

theorem space2271_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [163, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(163, 247), (84, 163), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    det267 det318 inv318
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space2271_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 467 space2271_orbit
  simpa only [lower467] using h


end QiushiMatmul.FrozenWang
