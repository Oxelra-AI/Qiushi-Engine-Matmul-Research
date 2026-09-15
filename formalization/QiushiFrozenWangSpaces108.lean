import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3456_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 213, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (213, 372), (10, 96)]
    (codeMat 205) (codeMat 419) (codeMat 183) false
    det205 det419 inv419
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3456_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 213, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3456_orbit
  simpa only [lower476] using h

theorem space3457_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 214, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 94), (214, 84), (10, 300)]
    (codeMat 397) (codeMat 358) (codeMat 158) false
    det397 det358 inv358
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3457_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 214, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3457_orbit
  simpa only [lower474] using h

theorem space3458_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 215, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 299), (215, 94), (10, 383)]
    (codeMat 174) (codeMat 442) (codeMat 334) false
    det174 det442 inv442
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3458_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 215, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3458_orbit
  simpa only [lower471] using h

theorem space3459_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 224, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 94), (224, 240), (10, 164)]
    (codeMat 183) (codeMat 396) (codeMat 106) false
    det183 det396 inv396
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3459_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 224, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space3459_orbit
  simpa only [lower468] using h

theorem space3460_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 226, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (226, 94), (10, 294)]
    (codeMat 305) (codeMat 244) (codeMat 95) false
    det305 det244 inv244
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3460_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 226, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3460_orbit
  simpa only [lower474] using h

theorem space3461_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 227, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (227, 376), (10, 300)]
    (codeMat 342) (codeMat 421) (codeMat 179) false
    det342 det421 inv421
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3461_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 227, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3461_orbit
  simpa only [lower474] using h

theorem space3462_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [275, 228, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(275, 250), (228, 78), (10, 68)]
    (codeMat 115) (codeMat 486) (codeMat 157) false
    det115 det486 inv486
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space3462_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 228, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space3462_orbit
  simpa only [lower464] using h

theorem space3463_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 229, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 94), (229, 84), (10, 264)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    det95 det419 inv419
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3463_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 229, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3463_orbit
  simpa only [lower469] using h

theorem space3464_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 231, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 314), (231, 78), (10, 68)]
    (codeMat 123) (codeMat 486) (codeMat 157) false
    det123 det486 inv486
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3464_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 231, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3464_orbit
  simpa only [lower465] using h

theorem space3465_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 240, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 286), (240, 276), (10, 96)]
    (codeMat 179) (codeMat 236) (codeMat 123) true
    det179 det236 inv236
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3465_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 240, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3465_orbit
  simpa only [lower476] using h

theorem space3466_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 241, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 286), (241, 372), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    det214 det355 inv355
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3466_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 241, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3466_orbit
  simpa only [lower476] using h

theorem space3467_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 242, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 84), (242, 303), (10, 293)]
    (codeMat 354) (codeMat 229) (codeMat 187) false
    det354 det229 inv229
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3467_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 242, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3467_orbit
  simpa only [lower473] using h

theorem space3468_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 243, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 84), (243, 289), (10, 383)]
    (codeMat 117) (codeMat 377) (codeMat 369) false
    det117 det377 inv377
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3468_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 243, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3468_orbit
  simpa only [lower471] using h

theorem space3469_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 244, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 342), (244, 84), (10, 264)]
    (codeMat 159) (codeMat 355) (codeMat 190) false
    det159 det355 inv355
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3469_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 244, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3469_orbit
  simpa only [lower469] using h

theorem space3470_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [275, 245, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(275, 253), (245, 10), (10, 68)]
    (codeMat 107) (codeMat 486) (codeMat 157) false
    det107 det486 inv486
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space3470_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 245, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space3470_orbit
  simpa only [lower463] using h

theorem space3471_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 246, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 382), (246, 10), (10, 68)]
    (codeMat 187) (codeMat 485) (codeMat 171) false
    det187 det485 inv485
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3471_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 246, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3471_orbit
  simpa only [lower465] using h

theorem space3472_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 247, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 379), (247, 94), (10, 10)]
    (codeMat 331) (codeMat 286) (codeMat 303) false
    det331 det286 inv286
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3472_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 247, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3472_orbit
  simpa only [lower473] using h

theorem space3473_orbit :
    frozenWangTable.OrbitImage 434 (spanCodes [273, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 434 [(273, 266), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis434]; decide +kernel)
    (by rw [basis434]; decide +kernel)

theorem space3473_lower : 17 ≤ frozenWangTable.L0 (spanCodes [273, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 434 space3473_orbit
  simpa only [lower434] using h

theorem space3474_orbit :
    frozenWangTable.OrbitImage 434 (spanCodes [272, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 434 [(272, 283), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    det267 det275 inv275
    (by rw [basis434]; decide +kernel)
    (by rw [basis434]; decide +kernel)

theorem space3474_lower : 17 ≤ frozenWangTable.L0 (spanCodes [272, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 434 space3474_orbit
  simpa only [lower434] using h

theorem space3475_orbit :
    frozenWangTable.OrbitImage 434 (spanCodes [257, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 434 [(257, 283), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 267) (codeMat 282) false
    det275 det267 inv267
    (by rw [basis434]; decide +kernel)
    (by rw [basis434]; decide +kernel)

theorem space3475_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 434 space3475_orbit
  simpa only [lower434] using h

theorem space3476_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [260, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(260, 1), (23, 160), (10, 402)]
    (codeMat 85) (codeMat 205) (codeMat 242) true
    det85 det205 inv205
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space3476_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space3476_orbit
  simpa only [lower447] using h

theorem space3477_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 305), (33, 33), (10, 43), (5, 1)]
    (codeMat 345) (codeMat 465) (codeMat 465) false
    det345 det465 inv465
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3477_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 295 space3477_orbit
  simpa only [lower295] using h

theorem space3478_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 32, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 282), (32, 32), (10, 43), (5, 1)]
    (codeMat 337) (codeMat 339) (codeMat 467) false
    det337 det339 inv339
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3478_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 32, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 295 space3478_orbit
  simpa only [lower295] using h

theorem space3479_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [263, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(263, 283), (36, 32), (20, 33), (10, 43)]
    (codeMat 346) (codeMat 458) (codeMat 458) false
    det346 det458 inv458
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3479_lower : 17 ≤ frozenWangTable.L0 (spanCodes [263, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3479_orbit
  simpa only [lower295] using h

theorem space3480_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [275, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(275, 307), (51, 306), (10, 160)]
    (codeMat 86) (codeMat 84) (codeMat 84) true
    det86 det84 inv84
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space3480_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space3480_orbit
  simpa only [lower447] using h

theorem space3481_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 48, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 305), (48, 1), (10, 43), (4, 32)]
    (codeMat 394) (codeMat 395) (codeMat 474) false
    det394 det395 inv395
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3481_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 48, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 295 space3481_orbit
  simpa only [lower295] using h

theorem space3482_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [262, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(262, 283), (32, 32), (21, 10), (10, 43)]
    (codeMat 339) (codeMat 346) (codeMat 459) false
    det339 det346 inv346
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3482_lower : 17 ≤ frozenWangTable.L0 (spanCodes [262, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3482_orbit
  simpa only [lower295] using h

theorem space3483_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 49, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 314), (49, 10), (10, 43), (4, 32)]
    (codeMat 395) (codeMat 409) (codeMat 473) false
    det395 det409 inv409
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3483_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 49, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 295 space3483_orbit
  simpa only [lower295] using h

theorem space3484_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [275, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(275, 403), (55, 402), (10, 306)]
    (codeMat 87) (codeMat 157) (codeMat 486) true
    det87 det157 inv157
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space3484_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space3484_orbit
  simpa only [lower447] using h

theorem space3485_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [275, 83, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(275, 307), (83, 306), (10, 160)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    det140 det172 inv172
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space3485_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 83, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space3485_orbit
  simpa only [lower447] using h

theorem space3486_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [256, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(256, 1), (71, 20), (19, 472), (10, 312)]
    (codeMat 140) (codeMat 214) (codeMat 214) false
    det140 det214 inv214
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space3486_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space3486_orbit
  simpa only [lower373] using h

theorem space3487_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 71, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (71, 160), (54, 260), (10, 170)]
    (codeMat 334) (codeMat 190) (codeMat 355) false
    det334 det190 inv190
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3487_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 71, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3487_orbit
  simpa only [lower315] using h


end QiushiMatmul.FrozenWang
