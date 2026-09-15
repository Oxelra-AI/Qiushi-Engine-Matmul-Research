import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3424_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 119, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 84), (119, 289), (10, 383)]
    (codeMat 190) (codeMat 499) (codeMat 382) false
    det190 det499 inv499
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3424_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 119, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3424_orbit
  simpa only [lower471] using h

theorem space3425_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 129, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 116), (129, 10), (10, 30)]
    (codeMat 428) (codeMat 279) (codeMat 279) true
    det428 det279 inv279
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3425_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 129, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3425_orbit
  simpa only [lower454] using h

theorem space3426_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [275, 131, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(275, 171), (131, 20), (10, 30)]
    (codeMat 359) (codeMat 282) (codeMat 267) true
    det359 det282 inv282
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3426_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 131, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3426_orbit
  simpa only [lower456] using h

theorem space3427_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 132, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 94), (132, 240), (10, 164)]
    (codeMat 110) (codeMat 468) (codeMat 87) false
    det110 det468 inv468
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3427_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 132, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space3427_orbit
  simpa only [lower468] using h

theorem space3428_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 133, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 286), (133, 276), (10, 96)]
    (codeMat 106) (codeMat 116) (codeMat 92) true
    det106 det116 inv116
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3428_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 133, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3428_orbit
  simpa only [lower476] using h

theorem space3429_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 134, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 94), (134, 10), (10, 293)]
    (codeMat 425) (codeMat 98) (codeMat 140) false
    det425 det98 inv98
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3429_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 134, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3429_orbit
  simpa only [lower473] using h

theorem space3430_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 135, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (135, 376), (10, 294)]
    (codeMat 299) (codeMat 124) (codeMat 124) false
    det299 det124 inv124
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3430_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 135, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3430_orbit
  simpa only [lower474] using h

theorem space3431_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 145, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 106), (145, 20), (10, 30)]
    (codeMat 444) (codeMat 286) (codeMat 303) true
    det444 det286 inv286
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3431_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 145, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3431_orbit
  simpa only [lower454] using h

theorem space3432_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 148, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 286), (148, 276), (10, 96)]
    (codeMat 141) (codeMat 417) (codeMat 177) false
    det141 det417 inv417
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3432_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 148, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3432_orbit
  simpa only [lower476] using h

theorem space3433_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 150, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 370), (150, 376), (10, 300)]
    (codeMat 461) (codeMat 486) (codeMat 157) false
    det461 det486 inv486
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3433_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 150, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3433_orbit
  simpa only [lower474] using h

theorem space3434_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 151, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 84), (151, 289), (10, 383)]
    (codeMat 239) (codeMat 426) (codeMat 335) false
    det239 det426 inv426
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3434_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 151, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3434_orbit
  simpa only [lower471] using h

theorem space3435_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [275, 160, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(275, 190), (160, 78), (10, 68)]
    (codeMat 122) (codeMat 358) (codeMat 158) false
    det122 det358 inv358
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space3435_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 160, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space3435_orbit
  simpa only [lower464] using h

theorem space3436_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 161, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 342), (161, 84), (10, 264)]
    (codeMat 86) (codeMat 417) (codeMat 177) false
    det86 det417 inv417
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3436_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 161, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3436_orbit
  simpa only [lower469] using h

theorem space3437_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 162, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 382), (162, 78), (10, 68)]
    (codeMat 114) (codeMat 358) (codeMat 158) false
    det114 det358 inv358
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3437_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 162, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3437_orbit
  simpa only [lower465] using h

theorem space3438_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 164, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 250), (164, 240), (10, 164)]
    (codeMat 254) (codeMat 412) (codeMat 111) false
    det254 det412 inv412
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3438_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 164, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space3438_orbit
  simpa only [lower468] using h

theorem space3439_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 166, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 94), (166, 376), (10, 300)]
    (codeMat 351) (codeMat 423) (codeMat 181) false
    det351 det423 inv423
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3439_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 166, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3439_orbit
  simpa only [lower474] using h

theorem space3440_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 167, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 84), (167, 94), (10, 294)]
    (codeMat 313) (codeMat 116) (codeMat 92) false
    det313 det116 inv116
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3440_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 167, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3440_orbit
  simpa only [lower474] using h

theorem space3441_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [275, 176, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(275, 185), (176, 78), (10, 68)]
    (codeMat 106) (codeMat 358) (codeMat 158) false
    det106 det358 inv358
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space3441_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 176, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space3441_orbit
  simpa only [lower463] using h

theorem space3442_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 177, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 348), (177, 342), (10, 258)]
    (codeMat 179) (codeMat 124) (codeMat 124) false
    det179 det124 inv124
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3442_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 177, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3442_orbit
  simpa only [lower469] using h

theorem space3443_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [275, 178, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(275, 314), (178, 78), (10, 68)]
    (codeMat 242) (codeMat 359) (codeMat 174) false
    det242 det359 inv359
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space3443_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 178, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space3443_orbit
  simpa only [lower465] using h

theorem space3444_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 179, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 369), (179, 84), (10, 10)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    det330 det270 inv270
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3444_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 179, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3444_orbit
  simpa only [lower473] using h

theorem space3445_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 180, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (180, 276), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    det159 det481 inv481
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3445_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 180, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3445_orbit
  simpa only [lower476] using h

theorem space3446_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 181, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (181, 286), (10, 276)]
    (codeMat 159) (codeMat 377) (codeMat 369) true
    det159 det377 inv377
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3446_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 181, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3446_orbit
  simpa only [lower476] using h

theorem space3447_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 182, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 369), (182, 10), (10, 293)]
    (codeMat 355) (codeMat 103) (codeMat 188) false
    det355 det103 inv103
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3447_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 182, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3447_orbit
  simpa only [lower473] using h

theorem space3448_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [275, 183, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(275, 299), (183, 94), (10, 383)]
    (codeMat 125) (codeMat 491) (codeMat 375) false
    det125 det491 inv491
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3448_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 183, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3448_orbit
  simpa only [lower471] using h

theorem space3449_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 193, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 106), (193, 10), (10, 30)]
    (codeMat 492) (codeMat 277) (codeMat 277) true
    det492 det277 inv277
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3449_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 193, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3449_orbit
  simpa only [lower454] using h

theorem space3450_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [275, 194, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(275, 181), (194, 20), (10, 30)]
    (codeMat 358) (codeMat 266) (codeMat 266) true
    det358 det266 inv266
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space3450_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 194, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space3450_orbit
  simpa only [lower456] using h

theorem space3451_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 196, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 250), (196, 240), (10, 164)]
    (codeMat 111) (codeMat 340) (codeMat 85) false
    det111 det340 inv340
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3451_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 196, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space3451_orbit
  simpa only [lower468] using h

theorem space3452_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [275, 197, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(275, 382), (197, 276), (10, 96)]
    (codeMat 107) (codeMat 244) (codeMat 95) true
    det107 det244 inv244
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3452_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 197, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space3452_orbit
  simpa only [lower476] using h

theorem space3453_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [275, 198, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(275, 84), (198, 376), (10, 294)]
    (codeMat 298) (codeMat 236) (codeMat 123) false
    det298 det236 inv236
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3453_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 198, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3453_orbit
  simpa only [lower474] using h

theorem space3454_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [275, 199, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(275, 369), (199, 10), (10, 293)]
    (codeMat 417) (codeMat 230) (codeMat 159) false
    det417 det230 inv230
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3454_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 199, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space3454_orbit
  simpa only [lower473] using h

theorem space3455_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [275, 208, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(275, 116), (208, 10), (10, 30)]
    (codeMat 500) (codeMat 270) (codeMat 298) true
    det500 det270 inv270
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3455_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 208, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3455_orbit
  simpa only [lower454] using h


end QiushiMatmul.FrozenWang
