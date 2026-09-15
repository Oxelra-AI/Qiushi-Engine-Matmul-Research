import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2368_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [65, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(65, 2), (21, 297), (9, 1), (3, 32)]
    (codeMat 107) (codeMat 275) (codeMat 275) true
    det107 det275 inv275
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2368_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space2368_orbit
  simpa only [lower269] using h

theorem space2369_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [67, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(67, 138), (16, 1), (10, 10), (7, 32)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    det458 det302 inv302
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2369_lower : 16 ≤ frozenWangTable.L0 (spanCodes [67, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 292 space2369_orbit
  simpa only [lower292] using h

theorem space2370_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [67, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(67, 138), (17, 11), (10, 10), (6, 32)]
    (codeMat 459) (codeMat 318) (codeMat 299) false
    det459 det318 inv318
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2370_lower : 16 ≤ frozenWangTable.L0 (spanCodes [67, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 292 space2370_orbit
  simpa only [lower292] using h

theorem space2371_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [65, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(65, 2), (21, 264), (8, 1), (2, 32)]
    (codeMat 106) (codeMat 277) (codeMat 277) true
    det106 det277 inv277
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2371_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2371_orbit
  simpa only [lower269] using h

theorem space2372_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [84, 32, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(84, 84), (32, 2), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    det266 det161 inv161
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2372_lower : 16 ≤ frozenWangTable.L0 (spanCodes [84, 32, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space2372_orbit
  simpa only [lower267] using h

theorem space2373_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [84, 36, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(84, 117), (36, 3), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 167) (codeMat 167) false
    det267 det167 inv167
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2373_lower : 16 ≤ frozenWangTable.L0 (spanCodes [84, 36, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space2373_orbit
  simpa only [lower267] using h

theorem space2374_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [64, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(64, 384), (36, 32), (20, 33), (10, 43)]
    (codeMat 282) (codeMat 458) (codeMat 458) false
    det282 det458 inv458
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2374_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2374_orbit
  simpa only [lower298] using h

theorem space2375_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [67, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(67, 427), (39, 42), (23, 10), (10, 43)]
    (codeMat 467) (codeMat 382) (codeMat 499) false
    det467 det382 inv382
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2375_lower : 16 ≤ frozenWangTable.L0 (spanCodes [67, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2375_orbit
  simpa only [lower298] using h

theorem space2376_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [66, 36, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(66, 427), (36, 1), (22, 10), (10, 43)]
    (codeMat 403) (codeMat 94) (codeMat 500) false
    det403 det94 inv94
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2376_lower : 16 ≤ frozenWangTable.L0 (spanCodes [66, 36, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2376_orbit
  simpa only [lower298] using h

theorem space2377_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [65, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(65, 384), (39, 11), (21, 33), (10, 43)]
    (codeMat 346) (codeMat 234) (codeMat 461) false
    det346 det234 inv234
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2377_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2377_orbit
  simpa only [lower298] using h

theorem space2378_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [84, 48, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(84, 116), (48, 2), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    det266 det417 inv417
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2378_lower : 16 ≤ frozenWangTable.L0 (spanCodes [84, 48, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space2378_orbit
  simpa only [lower267] using h

theorem space2379_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [65, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(65, 384), (32, 32), (21, 10), (10, 43)]
    (codeMat 339) (codeMat 346) (codeMat 459) false
    det339 det346 inv346
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2379_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2379_orbit
  simpa only [lower298] using h

theorem space2380_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [67, 34, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(67, 427), (34, 42), (23, 33), (10, 43)]
    (codeMat 474) (codeMat 494) (codeMat 501) false
    det474 det494 inv494
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2380_lower : 16 ≤ frozenWangTable.L0 (spanCodes [67, 34, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2380_orbit
  simpa only [lower298] using h

theorem space2381_orbit :
    frozenWangTable.OrbitImage 324 (spanCodes [81, 48, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 324 [(81, 240), (48, 16), (10, 53), (5, 36)]
    (codeMat 467) (codeMat 431) (codeMat 477) false
    det467 det431 inv431
    (by rw [basis324]; decide +kernel)
    (by rw [basis324]; decide +kernel)

theorem space2381_lower : 16 ≤ frozenWangTable.L0 (spanCodes [81, 48, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 324 space2381_orbit
  simpa only [lower324] using h

theorem space2382_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [64, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(64, 384), (34, 11), (20, 10), (10, 43)]
    (codeMat 275) (codeMat 122) (codeMat 460) false
    det275 det122 inv122
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2382_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space2382_orbit
  simpa only [lower298] using h

theorem space2383_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [84, 53, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(84, 85), (53, 34), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 423) (codeMat 181) false
    det267 det423 inv423
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2383_lower : 16 ≤ frozenWangTable.L0 (spanCodes [84, 53, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space2383_orbit
  simpa only [lower267] using h

theorem space2384_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [128, 84, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(128, 2), (84, 84), (8, 32), (2, 1)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    det161 det266 inv266
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2384_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 84, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space2384_orbit
  simpa only [lower267] using h

theorem space2385_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [130, 83, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(130, 1), (83, 10), (10, 43), (7, 384)]
    (codeMat 501) (codeMat 299) (codeMat 318) true
    det501 det299 inv299
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2385_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 83, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 298 space2385_orbit
  simpa only [lower298] using h

theorem space2386_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [128, 82, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(128, 1), (82, 10), (10, 43), (6, 384)]
    (codeMat 444) (codeMat 271) (codeMat 314) true
    det444 det271 inv271
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2386_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 82, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 298 space2386_orbit
  simpa only [lower298] using h

theorem space2387_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [130, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(130, 32), (80, 10), (10, 43), (4, 384)]
    (codeMat 358) (codeMat 281) (codeMat 281) true
    det358 det281 inv281
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2387_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 298 space2387_orbit
  simpa only [lower298] using h

theorem space2388_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [133, 84, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(133, 119), (84, 85), (9, 32), (3, 1)]
    (codeMat 241) (codeMat 282) (codeMat 267) true
    det241 det282 inv282
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2388_lower : 16 ≤ frozenWangTable.L0 (spanCodes [133, 84, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space2388_orbit
  simpa only [lower267] using h

theorem space2389_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [144, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(144, 1), (80, 33), (10, 43), (4, 384)]
    (codeMat 302) (codeMat 267) (codeMat 282) true
    det302 det267 inv267
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2389_lower : 16 ≤ frozenWangTable.L0 (spanCodes [144, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 298 space2389_orbit
  simpa only [lower298] using h

theorem space2390_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [146, 82, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(146, 32), (82, 33), (10, 43), (6, 384)]
    (codeMat 500) (codeMat 313) (codeMat 313) true
    det500 det313 inv313
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2390_lower : 16 ≤ frozenWangTable.L0 (spanCodes [146, 82, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 298 space2390_orbit
  simpa only [lower298] using h

theorem space2391_orbit :
    frozenWangTable.OrbitImage 324 (spanCodes [128, 67, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 324 [(128, 16), (67, 17), (23, 240), (10, 53)]
    (codeMat 485) (codeMat 317) (codeMat 285) true
    det485 det317 inv317
    (by rw [basis324]; decide +kernel)
    (by rw [basis324]; decide +kernel)

theorem space2391_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 67, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 324 space2391_orbit
  simpa only [lower324] using h

theorem space2392_orbit :
    frozenWangTable.OrbitImage 274 (spanCodes [130, 65, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 274 [(130, 2), (65, 1), (21, 160), (10, 80)]
    (codeMat 141) (codeMat 277) (codeMat 277) false
    det141 det277 inv277
    (by rw [basis274]; decide +kernel)
    (by rw [basis274]; decide +kernel)

theorem space2392_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 65, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 274 space2392_orbit
  simpa only [lower274] using h

theorem space2393_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [144, 83, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(144, 32), (83, 33), (10, 43), (7, 384)]
    (codeMat 445) (codeMat 285) (codeMat 317) true
    det445 det285 inv285
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2393_lower : 16 ≤ frozenWangTable.L0 (spanCodes [144, 83, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 298 space2393_orbit
  simpa only [lower298] using h

theorem space2394_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [146, 81, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(146, 1), (81, 33), (10, 43), (5, 384)]
    (codeMat 359) (codeMat 303) (codeMat 286) true
    det359 det303 inv303
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space2394_lower : 16 ≤ frozenWangTable.L0 (spanCodes [146, 81, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 298 space2394_orbit
  simpa only [lower298] using h

theorem space2395_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [148, 84, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(148, 119), (84, 117), (9, 32), (3, 1)]
    (codeMat 225) (codeMat 314) (codeMat 271) true
    det225 det314 inv314
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2395_lower : 16 ≤ frozenWangTable.L0 (spanCodes [148, 84, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space2395_orbit
  simpa only [lower267] using h

theorem space2396_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [256, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(256, 1), (80, 96), (10, 272), (4, 2)]
    (codeMat 140) (codeMat 84) (codeMat 84) true
    det140 det84 inv84
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2396_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 276 space2396_orbit
  simpa only [lower276] using h

theorem space2397_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [260, 65, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(260, 3), (65, 2), (21, 96), (10, 272)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    det85 det172 inv172
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space2397_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 65, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space2397_orbit
  simpa only [lower276] using h

theorem space2398_orbit :
    frozenWangTable.OrbitImage 275 (spanCodes [260, 84, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 275 [(260, 1), (84, 244), (36, 2), (10, 160)]
    (codeMat 93) (codeMat 212) (codeMat 86) true
    det93 det212 inv212
    (by rw [basis275]; decide +kernel)
    (by rw [basis275]; decide +kernel)

theorem space2398_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 84, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 275 space2398_orbit
  simpa only [lower275] using h

theorem space2399_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [256, 84, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(256, 1), (84, 99), (36, 2), (10, 306)]
    (codeMat 156) (codeMat 87) (codeMat 468) true
    det156 det87 inv87
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2399_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 84, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2399_orbit
  simpa only [lower278] using h


end QiushiMatmul.FrozenWang
