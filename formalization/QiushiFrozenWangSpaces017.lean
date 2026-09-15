import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0544_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [258, 197, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(258, 495), (197, 493), (38, 463), (19, 441), (10, 119)]
    (codeMat 491) (codeMat 234) (codeMat 461) true
    det491 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0544_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 197, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0544_orbit
  simpa only [lower144] using h

theorem space0545_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 199, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (199, 34), (38, 440), (19, 462), (10, 119)]
    (codeMat 299) (codeMat 241) (codeMat 489) true
    det299 det241 inv241
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0545_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 199, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0545_orbit
  simpa only [lower144] using h

theorem space0546_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 135, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (135, 34), (38, 118), (19, 441), (10, 462)]
    (codeMat 299) (codeMat 346) (codeMat 459) true
    det299 det346 inv346
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0546_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 135, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0546_orbit
  simpa only [lower144] using h

theorem space0547_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [321, 134, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(321, 495), (134, 493), (38, 118), (19, 462), (10, 441)]
    (codeMat 491) (codeMat 375) (codeMat 491) true
    det491 det375 inv375
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0547_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 134, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0547_orbit
  simpa only [lower144] using h

theorem space0548_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [387, 68, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(387, 495), (68, 493), (38, 440), (19, 119), (10, 462)]
    (codeMat 491) (codeMat 409) (codeMat 473) true
    det491 det409 inv409
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0548_lower : 15 ≤ frozenWangTable.L0 (spanCodes [387, 68, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0548_orbit
  simpa only [lower144] using h

theorem space0549_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 71, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 32), (71, 34), (38, 463), (19, 119), (10, 441)]
    (codeMat 299) (codeMat 431) (codeMat 477) true
    det299 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0549_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 71, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0549_orbit
  simpa only [lower144] using h

theorem space0550_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (128, 1), (98, 85), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 106) (codeMat 396) false
    det372 det106 inv106
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0550_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0550_orbit
  simpa only [lower144] using h

theorem space0551_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 167, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (167, 85), (65, 1), (19, 119), (10, 462)]
    (codeMat 309) (codeMat 177) (codeMat 417) false
    det309 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0551_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 167, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0551_orbit
  simpa only [lower144] using h

theorem space0552_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 133, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (133, 411), (71, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 473) (codeMat 409) false
    det311 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0552_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0552_orbit
  simpa only [lower144] using h

theorem space0553_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 194, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 398), (194, 414), (34, 399), (19, 245), (10, 427)]
    (codeMat 486) (codeMat 213) (codeMat 470) false
    det486 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0553_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0553_orbit
  simpa only [lower220] using h

theorem space0554_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [325, 133, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(325, 2), (133, 34), (34, 118), (19, 441), (10, 119)]
    (codeMat 298) (codeMat 339) (codeMat 467) true
    det298 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0554_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 133, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0554_orbit
  simpa only [lower144] using h

theorem space0555_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 135, 67, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (135, 164), (67, 447), (34, 430), (19, 463), (10, 446)]
    (codeMat 279) (codeMat 181) (codeMat 423) false
    det279 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0555_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 67, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0555_orbit
  simpa only [lower69] using h

theorem space0556_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [385, 65, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(385, 208), (65, 192), (34, 399), (19, 350), (10, 427)]
    (codeMat 358) (codeMat 445) (codeMat 478) false
    det358 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0556_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 65, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0556_orbit
  simpa only [lower220] using h

theorem space0557_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 131, 70, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 191), (131, 447), (70, 283), (34, 97), (19, 446), (10, 113)]
    (codeMat 342) (codeMat 335) (codeMat 426) false
    det342 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0557_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 70, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0557_orbit
  simpa only [lower69] using h

theorem space0558_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 132, 71, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 257), (132, 197), (71, 196), (34, 430), (19, 113), (10, 446)]
    (codeMat 277) (codeMat 477) (codeMat 431) false
    det277 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0558_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 71, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0558_orbit
  simpa only [lower69] using h

theorem space0559_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 132, 70, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 353), (132, 180), (70, 378), (35, 97), (19, 113), (10, 446)]
    (codeMat 407) (codeMat 473) (codeMat 409) false
    det407 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0559_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 70, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0559_orbit
  simpa only [lower69] using h

theorem space0560_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 129, 68, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (129, 447), (68, 283), (35, 430), (19, 446), (10, 113)]
    (codeMat 279) (codeMat 111) (codeMat 412) false
    det279 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0560_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0560_orbit
  simpa only [lower69] using h

theorem space0561_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 133, 65, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 436), (133, 363), (65, 1), (32, 16), (19, 463), (10, 446)]
    (codeMat 405) (codeMat 177) (codeMat 417) false
    det405 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0561_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 65, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0561_orbit
  simpa only [lower69] using h

theorem space0562_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 130, 71, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 453), (130, 1), (71, 197), (32, 16), (19, 463), (10, 113)]
    (codeMat 277) (codeMat 106) (codeMat 396) false
    det277 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0562_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 130, 71, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0562_orbit
  simpa only [lower69] using h

theorem space0563_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 128, 70, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 223), (128, 1), (70, 362), (33, 479), (19, 446), (10, 113)]
    (codeMat 468) (codeMat 331) (codeMat 410) false
    det468 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0563_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 70, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0563_orbit
  simpa only [lower69] using h

theorem space0564_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 131, 71, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 175), (131, 462), (71, 180), (33, 430), (19, 463), (10, 113)]
    (codeMat 470) (codeMat 334) (codeMat 442) false
    det470 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0564_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 131, 71, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0564_orbit
  simpa only [lower69] using h

theorem space0565_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 131, 68, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (131, 447), (68, 283), (33, 479), (19, 446), (10, 113)]
    (codeMat 342) (codeMat 331) (codeMat 410) false
    det342 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0565_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 68, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0565_orbit
  simpa only [lower69] using h

theorem space0566_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 128, 69, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 257), (128, 1), (69, 197), (33, 430), (19, 463), (10, 113)]
    (codeMat 340) (codeMat 334) (codeMat 442) false
    det340 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0566_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 69, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0566_orbit
  simpa only [lower69] using h

theorem space0567_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 134, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (134, 283), (66, 447), (38, 479), (19, 113), (10, 446)]
    (codeMat 286) (codeMat 403) (codeMat 403) false
    det286 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0567_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0567_orbit
  simpa only [lower69] using h

theorem space0568_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 133, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 175), (133, 180), (66, 462), (38, 430), (19, 113), (10, 463)]
    (codeMat 478) (codeMat 405) (codeMat 407) false
    det478 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0568_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0568_orbit
  simpa only [lower69] using h

theorem space0569_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 135, 65, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 223), (135, 362), (65, 1), (38, 479), (19, 113), (10, 446)]
    (codeMat 477) (codeMat 403) (codeMat 403) false
    det477 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0569_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 65, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0569_orbit
  simpa only [lower69] using h

theorem space0570_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 132, 65, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 257), (132, 197), (65, 1), (38, 430), (19, 113), (10, 463)]
    (codeMat 285) (codeMat 405) (codeMat 407) false
    det285 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0570_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 132, 65, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0570_orbit
  simpa only [lower69] using h

theorem space0571_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 134, 67, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (134, 283), (67, 447), (39, 430), (19, 113), (10, 446)]
    (codeMat 351) (codeMat 183) (codeMat 419) false
    det351 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0571_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 67, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0571_orbit
  simpa only [lower69] using h

theorem space0572_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 135, 69, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 353), (135, 378), (69, 180), (39, 97), (19, 446), (10, 113)]
    (codeMat 415) (codeMat 474) (codeMat 395) false
    det415 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0572_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 69, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0572_orbit
  simpa only [lower69] using h

theorem space0573_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 133, 64, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 453), (133, 197), (64, 1), (36, 16), (19, 113), (10, 463)]
    (codeMat 348) (codeMat 177) (codeMat 417) false
    det348 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0573_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 64, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0573_orbit
  simpa only [lower69] using h

theorem space0574_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 128, 71, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 436), (128, 1), (71, 363), (36, 16), (19, 446), (10, 463)]
    (codeMat 412) (codeMat 106) (codeMat 396) false
    det412 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0574_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 71, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0574_orbit
  simpa only [lower69] using h

theorem space0575_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [261, 194, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(261, 398), (194, 414), (37, 399), (19, 427), (10, 245)]
    (codeMat 494) (codeMat 206) (codeMat 498) false
    det494 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0575_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 194, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0575_orbit
  simpa only [lower220] using h


end QiushiMatmul.FrozenWang
