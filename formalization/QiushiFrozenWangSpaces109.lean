import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3488_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 70, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 421), (70, 160), (50, 430), (10, 170)]
    (codeMat 335) (codeMat 174) (codeMat 359) false
    det335 det174 inv174
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3488_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 70, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3488_orbit
  simpa only [lower315] using h

theorem space3489_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [275, 147, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(275, 403), (147, 402), (10, 160)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    det84 det116 inv116
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space3489_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 147, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space3489_orbit
  simpa only [lower447] using h

theorem space3490_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 162, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (162, 10), (10, 170), (7, 260)]
    (codeMat 407) (codeMat 117) (codeMat 380) false
    det407 det117 inv117
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3490_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 162, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 315 space3490_orbit
  simpa only [lower315] using h

theorem space3491_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 149, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 421), (149, 420), (39, 430), (10, 170)]
    (codeMat 405) (codeMat 125) (codeMat 348) false
    det405 det125 inv125
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3491_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 149, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3491_orbit
  simpa only [lower315] using h

theorem space3492_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 129, 65, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 282), (129, 33), (65, 1), (10, 43)]
    (codeMat 309) (codeMat 279) (codeMat 279) true
    det309 det279 inv279
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3492_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 129, 65, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3492_orbit
  simpa only [lower295] using h

theorem space3493_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 144, 80, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 305), (144, 1), (80, 33), (10, 43)]
    (codeMat 302) (codeMat 271) (codeMat 314) true
    det302 det271 inv271
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3493_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 144, 80, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3493_orbit
  simpa only [lower295] using h

theorem space3494_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 128, 65, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 305), (128, 32), (65, 1), (10, 43)]
    (codeMat 317) (codeMat 277) (codeMat 277) true
    det317 det277 inv277
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3494_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 128, 65, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3494_orbit
  simpa only [lower295] using h

theorem space3495_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 178, 113, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (178, 170), (113, 430), (10, 160)]
    (codeMat 214) (codeMat 380) (codeMat 117) false
    det214 det380 inv380
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3495_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 178, 113, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3495_orbit
  simpa only [lower315] using h

theorem space3496_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 144, 64, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 282), (144, 1), (64, 32), (10, 43)]
    (codeMat 318) (codeMat 270) (codeMat 298) true
    det318 det270 inv270
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3496_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 144, 64, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3496_orbit
  simpa only [lower295] using h

theorem space3497_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 128, 81, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 282), (128, 32), (81, 10), (10, 43)]
    (codeMat 303) (codeMat 285) (codeMat 317) true
    det303 det285 inv285
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3497_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 128, 81, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3497_orbit
  simpa only [lower295] using h

theorem space3498_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [275, 145, 64, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(275, 305), (145, 10), (64, 32), (10, 43)]
    (codeMat 311) (codeMat 286) (codeMat 303) true
    det311 det286 inv286
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space3498_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 145, 64, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space3498_orbit
  simpa only [lower295] using h

theorem space3499_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 149, 71, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 431), (149, 430), (71, 10), (10, 160)]
    (codeMat 205) (codeMat 444) (codeMat 110) false
    det205 det444 inv444
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3499_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 149, 71, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3499_orbit
  simpa only [lower315] using h

theorem space3500_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 146, 70, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (146, 260), (70, 10), (10, 160)]
    (codeMat 141) (codeMat 428) (codeMat 107) false
    det141 det428 inv428
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3500_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 146, 70, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3500_orbit
  simpa only [lower315] using h

theorem space3501_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 162, 67, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 431), (162, 170), (67, 420), (10, 160)]
    (codeMat 86) (codeMat 372) (codeMat 93) false
    det86 det372 inv372
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3501_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 162, 67, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3501_orbit
  simpa only [lower315] using h

theorem space3502_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 165, 66, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (165, 270), (66, 420), (10, 160)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    det95 det500 inv500
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3502_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 165, 66, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3502_orbit
  simpa only [lower315] using h

theorem space3503_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 225, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 421), (225, 270), (10, 170), (6, 260)]
    (codeMat 478) (codeMat 247) (codeMat 379) false
    det478 det247 inv247
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3503_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 225, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 315 space3503_orbit
  simpa only [lower315] using h

theorem space3504_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 130, 116, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 431), (130, 260), (116, 270), (10, 160)]
    (codeMat 159) (codeMat 492) (codeMat 115) false
    det159 det492 inv492
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3504_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 130, 116, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3504_orbit
  simpa only [lower315] using h

theorem space3505_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 212, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (212, 270), (34, 430), (10, 170)]
    (codeMat 477) (codeMat 239) (codeMat 351) false
    det477 det239 inv239
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3505_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 212, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space3505_orbit
  simpa only [lower315] using h

theorem space3506_orbit :
    frozenWangTable.OrbitImage 373 (spanCodes [256, 229, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 373 [(256, 1), (229, 460), (19, 472), (10, 312)]
    (codeMat 92) (codeMat 95) (codeMat 244) false
    det92 det95 inv95
    (by rw [basis373]; decide +kernel)
    (by rw [basis373]; decide +kernel)

theorem space3506_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 229, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 373 space3506_orbit
  simpa only [lower373] using h

theorem space3507_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [273, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(273, 84), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    det273 det84 inv84
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3507_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space3507_orbit
  simpa only [lower267] using h

theorem space3508_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [272, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(272, 118), (9, 32), (4, 1), (3, 2)]
    (codeMat 281) (codeMat 212) (codeMat 86) false
    det281 det212 inv212
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3508_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space3508_orbit
  simpa only [lower267] using h

theorem space3509_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [273, 32, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(273, 84), (32, 1), (8, 2), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3509_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 32, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 267 space3509_orbit
  simpa only [lower267] using h

theorem space3510_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [272, 36, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(272, 118), (36, 1), (9, 2), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    det267 det156 inv156
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3510_lower : 16 ≤ frozenWangTable.L0 (spanCodes [272, 36, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space3510_orbit
  simpa only [lower267] using h

theorem space3511_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [260, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(260, 384), (39, 43), (23, 11), (10, 42)]
    (codeMat 339) (codeMat 377) (codeMat 369) false
    det339 det377 inv377
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3511_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3511_orbit
  simpa only [lower298] using h

theorem space3512_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [257, 32, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(257, 118), (32, 1), (18, 32), (10, 34)]
    (codeMat 282) (codeMat 204) (codeMat 114) false
    det282 det204 inv204
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3512_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 32, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space3512_orbit
  simpa only [lower267] using h

theorem space3513_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [260, 34, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(260, 384), (34, 43), (23, 33), (10, 42)]
    (codeMat 346) (codeMat 491) (codeMat 375) false
    det346 det491 inv491
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3513_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 34, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3513_orbit
  simpa only [lower298] using h

theorem space3514_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 51, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 395), (51, 11), (10, 42), (6, 1)]
    (codeMat 409) (codeMat 499) (codeMat 382) false
    det409 det499 inv499
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3514_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 51, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 298 space3514_orbit
  simpa only [lower298] using h

theorem space3515_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [257, 36, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(257, 118), (36, 1), (18, 2), (10, 34)]
    (codeMat 275) (codeMat 92) (codeMat 116) false
    det275 det92 inv92
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3515_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 36, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space3515_orbit
  simpa only [lower267] using h

theorem space3516_orbit :
    frozenWangTable.OrbitImage 274 (spanCodes [275, 48, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 274 [(275, 242), (48, 1), (10, 83), (6, 3)]
    (codeMat 346) (codeMat 122) (codeMat 460) true
    det346 det122 inv122
    (by rw [basis274]; decide +kernel)
    (by rw [basis274]; decide +kernel)

theorem space3516_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 48, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 274 space3516_orbit
  simpa only [lower274] using h

theorem space3517_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 51, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 417), (51, 33), (10, 42), (5, 32)]
    (codeMat 395) (codeMat 442) (codeMat 334) false
    det395 det442 inv442
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3517_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 51, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 298 space3517_orbit
  simpa only [lower298] using h

theorem space3518_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 48, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 417), (48, 32), (10, 42), (7, 1)]
    (codeMat 465) (codeMat 369) (codeMat 377) false
    det465 det369 inv369
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3518_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 48, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 298 space3518_orbit
  simpa only [lower298] using h

theorem space3519_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 50, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 395), (50, 43), (10, 42), (5, 32)]
    (codeMat 458) (codeMat 426) (codeMat 335) false
    det458 det426 inv426
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3519_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 50, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 298 space3519_orbit
  simpa only [lower298] using h


end QiushiMatmul.FrozenWang
