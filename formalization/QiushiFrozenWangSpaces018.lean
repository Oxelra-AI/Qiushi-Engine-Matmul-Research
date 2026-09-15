import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0576_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [327, 128, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(327, 208), (128, 192), (37, 399), (19, 427), (10, 350)]
    (codeMat 302) (codeMat 382) (codeMat 499) false
    det302 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0576_lower : 15 ≤ frozenWangTable.L0 (spanCodes [327, 128, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0576_orbit
  simpa only [lower220] using h

theorem space0577_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 135, 66, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 191), (135, 283), (66, 447), (37, 97), (19, 113), (10, 446)]
    (codeMat 286) (codeMat 407) (codeMat 405) false
    det286 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0577_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0577_orbit
  simpa only [lower69] using h

theorem space0578_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 132, 66, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 353), (132, 180), (66, 462), (37, 97), (19, 113), (10, 463)]
    (codeMat 478) (codeMat 401) (codeMat 401) false
    det478 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0578_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 132, 66, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0578_orbit
  simpa only [lower69] using h

theorem space0579_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 129, 70, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (129, 447), (70, 164), (37, 430), (19, 446), (10, 463)]
    (codeMat 351) (codeMat 110) (codeMat 444) false
    det351 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0579_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 70, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0579_orbit
  simpa only [lower69] using h

theorem space0580_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 133, 69, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 257), (133, 196), (69, 197), (37, 430), (19, 446), (10, 113)]
    (codeMat 348) (codeMat 478) (codeMat 445) false
    det348 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0580_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 69, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0580_orbit
  simpa only [lower69] using h

theorem space0581_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [289, 129, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(289, 68), (129, 28), (64, 3), (17, 20), (8, 2), (2, 32)]
    (codeMat 86) (codeMat 273) (codeMat 273) true
    det86 det273 inv273
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0581_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 129, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0581_orbit
  simpa only [lower31] using h

theorem space0582_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 166, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 32), (166, 35), (101, 34), (19, 441), (10, 119)]
    (codeMat 309) (codeMat 474) (codeMat 395) false
    det309 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0582_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0582_orbit
  simpa only [lower144] using h

theorem space0583_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 163, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (163, 410), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 183) (codeMat 419) false
    det372 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0583_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0583_orbit
  simpa only [lower144] using h

theorem space0584_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 195, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 208), (195, 192), (35, 209), (19, 245), (10, 350)]
    (codeMat 358) (codeMat 206) (codeMat 498) false
    det358 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0584_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 195, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0584_orbit
  simpa only [lower220] using h

theorem space0585_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [321, 129, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(321, 398), (129, 414), (35, 378), (19, 350), (10, 245)]
    (codeMat 486) (codeMat 382) (codeMat 499) false
    det486 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0585_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 129, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0585_orbit
  simpa only [lower220] using h

theorem space0586_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 134, 66, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (134, 164), (66, 447), (35, 479), (19, 463), (10, 446)]
    (codeMat 342) (codeMat 401) (codeMat 401) false
    det342 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0586_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 66, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0586_orbit
  simpa only [lower69] using h

theorem space0587_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 66, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 175), (132, 378), (66, 462), (35, 430), (19, 446), (10, 463)]
    (codeMat 470) (codeMat 407) (codeMat 405) false
    det470 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0587_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 66, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0587_orbit
  simpa only [lower69] using h

theorem space0588_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 133, 71, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 191), (133, 283), (71, 164), (35, 97), (19, 113), (10, 463)]
    (codeMat 279) (codeMat 478) (codeMat 445) false
    det279 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0588_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 71, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0588_orbit
  simpa only [lower69] using h

theorem space0589_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [390, 70, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(390, 2), (70, 34), (35, 463), (19, 462), (10, 441)]
    (codeMat 298) (codeMat 445) (codeMat 478) true
    det298 det445 inv445
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0589_lower : 15 ≤ frozenWangTable.L0 (spanCodes [390, 70, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0589_orbit
  simpa only [lower144] using h

theorem space0590_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 130, 69, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 452), (130, 1), (69, 197), (35, 479), (19, 463), (10, 113)]
    (codeMat 277) (codeMat 110) (codeMat 444) false
    det277 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0590_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 130, 69, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0590_orbit
  simpa only [lower69] using h

theorem space0591_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 134, 65, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 452), (134, 196), (65, 1), (34, 479), (19, 446), (10, 463)]
    (codeMat 277) (codeMat 183) (codeMat 419) false
    det277 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0591_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 65, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0591_orbit
  simpa only [lower69] using h

theorem space0592_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 133, 70, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 223), (133, 362), (70, 363), (34, 479), (19, 113), (10, 463)]
    (codeMat 405) (codeMat 474) (codeMat 395) false
    det405 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0592_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 70, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0592_orbit
  simpa only [lower69] using h

theorem space0593_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 135, 66, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 191), (135, 164), (66, 447), (33, 97), (19, 463), (10, 446)]
    (codeMat 342) (codeMat 405) (codeMat 407) false
    det342 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0593_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 66, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0593_orbit
  simpa only [lower69] using h

theorem space0594_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 133, 66, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 353), (133, 378), (66, 462), (33, 97), (19, 446), (10, 463)]
    (codeMat 470) (codeMat 403) (codeMat 403) false
    det470 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0594_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 133, 66, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0594_orbit
  simpa only [lower69] using h

theorem space0595_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 134, 64, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (134, 196), (64, 1), (33, 97), (19, 446), (10, 463)]
    (codeMat 340) (codeMat 403) (codeMat 403) false
    det340 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0595_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 64, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0595_orbit
  simpa only [lower69] using h

theorem space0596_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 64, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 222), (132, 363), (64, 1), (33, 97), (19, 463), (10, 446)]
    (codeMat 468) (codeMat 405) (codeMat 407) false
    det468 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0596_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 64, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0596_orbit
  simpa only [lower69] using h

theorem space0597_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 134, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 420), (134, 164), (67, 447), (32, 16), (19, 463), (10, 446)]
    (codeMat 279) (codeMat 177) (codeMat 417) false
    det279 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0597_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0597_orbit
  simpa only [lower69] using h

theorem space0598_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 129, 69, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 469), (129, 462), (69, 180), (32, 16), (19, 463), (10, 113)]
    (codeMat 407) (codeMat 106) (codeMat 396) false
    det407 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0598_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 69, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0598_orbit
  simpa only [lower69] using h

theorem space0599_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 135, 64, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 437), (135, 362), (64, 1), (39, 430), (19, 113), (10, 446)]
    (codeMat 412) (codeMat 183) (codeMat 419) false
    det412 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0599_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 64, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0599_orbit
  simpa only [lower69] using h

theorem space0600_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 134, 70, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (134, 196), (70, 197), (39, 97), (19, 446), (10, 113)]
    (codeMat 348) (codeMat 474) (codeMat 395) false
    det348 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0600_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 70, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0600_orbit
  simpa only [lower69] using h

theorem space0601_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 71, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 437), (132, 363), (71, 362), (38, 430), (19, 463), (10, 113)]
    (codeMat 477) (codeMat 253) (codeMat 415) false
    det477 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0601_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 71, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0601_orbit
  simpa only [lower69] using h

theorem space0602_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 135, 70, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (135, 378), (70, 180), (38, 479), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 254) (codeMat 443) false
    det478 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0602_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 70, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0602_orbit
  simpa only [lower69] using h

theorem space0603_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 134, 69, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 452), (134, 196), (69, 197), (38, 479), (19, 446), (10, 113)]
    (codeMat 285) (codeMat 254) (codeMat 443) false
    det285 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0603_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 69, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0603_orbit
  simpa only [lower69] using h

theorem space0604_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 133, 68, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (133, 164), (68, 283), (38, 430), (19, 463), (10, 113)]
    (codeMat 286) (codeMat 253) (codeMat 415) false
    det286 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0604_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0604_orbit
  simpa only [lower69] using h

theorem space0605_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 129, 71, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (129, 462), (71, 378), (37, 479), (19, 463), (10, 446)]
    (codeMat 415) (codeMat 111) (codeMat 412) false
    det415 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0605_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 71, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0605_orbit
  simpa only [lower69] using h

theorem space0606_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 134, 68, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (134, 164), (68, 283), (37, 479), (19, 463), (10, 113)]
    (codeMat 351) (codeMat 473) (codeMat 409) false
    det351 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0606_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 68, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0606_orbit
  simpa only [lower69] using h

theorem space0607_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 199, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (199, 34), (36, 1), (19, 462), (10, 119)]
    (codeMat 355) (codeMat 213) (codeMat 470) true
    det355 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0607_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 199, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0607_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
