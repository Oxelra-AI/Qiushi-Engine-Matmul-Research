import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0448_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 135, 70, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (135, 180), (70, 378), (33, 479), (19, 113), (10, 446)]
    (codeMat 470) (codeMat 253) (codeMat 415) false
    det470 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0448_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 70, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0448_orbit
  simpa only [lower69] using h

theorem space0449_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 134, 71, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (134, 283), (71, 164), (33, 430), (19, 113), (10, 463)]
    (codeMat 342) (codeMat 254) (codeMat 443) false
    det342 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0449_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 71, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0449_orbit
  simpa only [lower69] using h

theorem space0450_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 133, 67, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (133, 378), (67, 462), (34, 479), (19, 446), (10, 463)]
    (codeMat 407) (codeMat 183) (codeMat 419) false
    det407 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0450_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 67, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0450_orbit
  simpa only [lower69] using h

theorem space0451_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 134, 68, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (134, 283), (68, 164), (34, 479), (19, 113), (10, 463)]
    (codeMat 279) (codeMat 474) (codeMat 395) false
    det279 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0451_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 68, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0451_orbit
  simpa only [lower69] using h

theorem space0452_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 135, 68, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (135, 197), (68, 196), (35, 97), (19, 113), (10, 446)]
    (codeMat 277) (codeMat 473) (codeMat 409) false
    det277 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0452_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 68, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0452_orbit
  simpa only [lower69] using h

theorem space0453_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 130, 70, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 437), (130, 1), (70, 362), (35, 430), (19, 446), (10, 113)]
    (codeMat 405) (codeMat 111) (codeMat 412) false
    det405 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0453_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 130, 70, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0453_orbit
  simpa only [lower69] using h

theorem space0454_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 132, 67, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 469), (132, 180), (67, 462), (36, 16), (19, 113), (10, 463)]
    (codeMat 415) (codeMat 177) (codeMat 417) false
    det415 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0454_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 67, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0454_orbit
  simpa only [lower69] using h

theorem space0455_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 129, 68, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 420), (129, 447), (68, 164), (36, 16), (19, 446), (10, 463)]
    (codeMat 351) (codeMat 106) (codeMat 396) false
    det351 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0455_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0455_orbit
  simpa only [lower69] using h

theorem space0456_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 128, 68, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 452), (128, 1), (68, 196), (37, 479), (19, 463), (10, 446)]
    (codeMat 348) (codeMat 111) (codeMat 412) false
    det348 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0456_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 68, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0456_orbit
  simpa only [lower69] using h

theorem space0457_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 135, 71, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 223), (135, 363), (71, 362), (37, 479), (19, 463), (10, 113)]
    (codeMat 412) (codeMat 473) (codeMat 409) false
    det412 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0457_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 71, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0457_orbit
  simpa only [lower69] using h

theorem space0458_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 130, 68, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (130, 1), (68, 196), (38, 97), (19, 463), (10, 446)]
    (codeMat 285) (codeMat 331) (codeMat 410) false
    det285 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0458_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 68, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0458_orbit
  simpa only [lower69] using h

theorem space0459_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 130, 69, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 222), (130, 1), (69, 363), (38, 97), (19, 446), (10, 463)]
    (codeMat 477) (codeMat 334) (codeMat 442) false
    det477 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0459_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 69, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0459_orbit
  simpa only [lower69] using h

theorem space0460_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 131, 70, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 191), (131, 447), (70, 164), (38, 97), (19, 446), (10, 463)]
    (codeMat 286) (codeMat 334) (codeMat 442) false
    det286 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0460_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 70, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0460_orbit
  simpa only [lower69] using h

theorem space0461_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 131, 71, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 353), (131, 462), (71, 378), (38, 97), (19, 463), (10, 446)]
    (codeMat 478) (codeMat 331) (codeMat 410) false
    det478 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0461_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 71, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0461_orbit
  simpa only [lower69] using h

theorem space0462_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [263, 192, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(263, 208), (192, 192), (39, 209), (19, 350), (10, 245)]
    (codeMat 302) (codeMat 213) (codeMat 470) false
    det302 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0462_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 192, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0462_orbit
  simpa only [lower220] using h

theorem space0463_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 135, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (135, 34), (39, 463), (19, 441), (10, 462)]
    (codeMat 355) (codeMat 382) (codeMat 499) true
    det355 det382 inv382
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0463_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 135, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0463_orbit
  simpa only [lower144] using h

theorem space0464_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 132, 64, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 452), (132, 197), (64, 1), (39, 479), (19, 113), (10, 463)]
    (codeMat 348) (codeMat 181) (codeMat 423) false
    det348 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0464_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 64, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0464_orbit
  simpa only [lower69] using h

theorem space0465_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [388, 67, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(388, 398), (67, 414), (39, 378), (19, 245), (10, 350)]
    (codeMat 494) (codeMat 445) (codeMat 478) false
    det494 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0465_lower : 15 ≤ frozenWangTable.L0 (spanCodes [388, 67, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0465_orbit
  simpa only [lower220] using h

theorem space0466_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 131, 68, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (131, 447), (68, 164), (39, 479), (19, 446), (10, 463)]
    (codeMat 286) (codeMat 330) (codeMat 394) false
    det286 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0466_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 68, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0466_orbit
  simpa only [lower69] using h

theorem space0467_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 131, 69, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 175), (131, 462), (69, 378), (39, 430), (19, 463), (10, 446)]
    (codeMat 478) (codeMat 335) (codeMat 426) false
    det478 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0467_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 69, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0467_orbit
  simpa only [lower69] using h

theorem space0468_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 133, 71, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 191), (133, 164), (71, 283), (39, 97), (19, 463), (10, 113)]
    (codeMat 351) (codeMat 477) (codeMat 431) false
    det351 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0468_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 71, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0468_orbit
  simpa only [lower69] using h

theorem space0469_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [289, 161, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(289, 495), (161, 492), (97, 493), (19, 119), (10, 441)]
    (codeMat 372) (codeMat 477) (codeMat 431) false
    det372 det477 inv477
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0469_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 161, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0469_orbit
  simpa only [lower144] using h

theorem space0470_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (160, 35), (97, 411), (19, 119), (10, 462)]
    (codeMat 358) (codeMat 254) (codeMat 443) false
    det358 det254 inv254
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0470_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0470_orbit
  simpa only [lower144] using h

theorem space0471_orbit :
    frozenWangTable.OrbitImage 231 (spanCodes [292, 164, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 231 [(292, 511), (164, 255), (97, 495), (19, 371), (10, 413)]
    (codeMat 302) (codeMat 375) (codeMat 491) false
    det302 det375 inv375
    (by rw [basis231]; decide +kernel)
    (by rw [basis231]; decide +kernel)

theorem space0471_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 231 space0471_orbit
  simpa only [lower231] using h

theorem space0472_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (128, 1), (97, 411), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 110) (codeMat 444) false
    det372 det110 inv110
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0472_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0472_orbit
  simpa only [lower144] using h

theorem space0473_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 131, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 408), (131, 440), (97, 493), (19, 441), (10, 119)]
    (codeMat 358) (codeMat 335) (codeMat 426) false
    det358 det335 inv335
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0473_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0473_orbit
  simpa only [lower144] using h

theorem space0474_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 161, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (161, 410), (96, 34), (19, 119), (10, 462)]
    (codeMat 358) (codeMat 250) (codeMat 397) false
    det358 det250 inv250
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0474_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 161, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0474_orbit
  simpa only [lower144] using h

theorem space0475_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 131, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (131, 440), (98, 84), (19, 441), (10, 119)]
    (codeMat 358) (codeMat 331) (codeMat 410) false
    det358 det331 inv331
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0475_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0475_orbit
  simpa only [lower144] using h

theorem space0476_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 164, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (164, 411), (101, 35), (19, 462), (10, 119)]
    (codeMat 302) (codeMat 253) (codeMat 415) false
    det302 det253 inv253
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0476_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 164, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0476_orbit
  simpa only [lower144] using h

theorem space0477_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [290, 164, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(290, 495), (164, 493), (103, 492), (19, 441), (10, 119)]
    (codeMat 309) (codeMat 478) (codeMat 445) false
    det309 det478 inv478
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0477_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 164, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0477_orbit
  simpa only [lower144] using h

theorem space0478_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 166, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (166, 34), (103, 410), (19, 462), (10, 119)]
    (codeMat 302) (codeMat 249) (codeMat 425) false
    det302 det249 inv249
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0478_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0478_orbit
  simpa only [lower144] using h

theorem space0479_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 130, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (130, 1), (103, 84), (19, 462), (10, 441)]
    (codeMat 309) (codeMat 107) (codeMat 428) false
    det309 det107 inv107
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0479_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0479_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
