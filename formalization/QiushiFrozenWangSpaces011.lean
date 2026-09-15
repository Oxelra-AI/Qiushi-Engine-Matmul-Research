import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0352_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 193, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 37), (193, 53), (19, 427), (10, 350), (5, 36)]
    (codeMat 421) (codeMat 213) (codeMat 470) false
    det421 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0352_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 193, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0352_orbit
  simpa only [lower220] using h

theorem space0353_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [354, 162, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(354, 443), (162, 411), (19, 119), (10, 441), (5, 1)]
    (codeMat 305) (codeMat 382) (codeMat 499) true
    det305 det382 inv382
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0353_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 162, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0353_orbit
  simpa only [lower144] using h

theorem space0354_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [387, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(387, 37), (67, 53), (19, 427), (10, 245), (5, 36)]
    (codeMat 485) (codeMat 445) (codeMat 478) false
    det485 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0354_lower : 15 ≤ frozenWangTable.L0 (spanCodes [387, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0354_orbit
  simpa only [lower220] using h

theorem space0355_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 163, 66, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 11), (163, 379), (66, 112), (19, 446), (10, 113), (5, 16)]
    (codeMat 270) (codeMat 181) (codeMat 423) false
    det270 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0355_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 163, 66, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0355_orbit
  simpa only [lower69] using h

theorem space0356_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 130, 96, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 352), (130, 1), (96, 378), (19, 113), (10, 463), (5, 16)]
    (codeMat 461) (codeMat 335) (codeMat 426) false
    det461 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0356_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 130, 96, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0356_orbit
  simpa only [lower69] using h

theorem space0357_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 161, 99, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 368), (161, 213), (99, 165), (19, 446), (10, 463), (5, 16)]
    (codeMat 271) (codeMat 477) (codeMat 431) false
    det271 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0357_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 161, 99, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0357_orbit
  simpa only [lower69] using h

theorem space0358_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 130, 98, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (130, 1), (98, 282), (19, 113), (10, 446), (5, 16)]
    (codeMat 397) (codeMat 330) (codeMat 394) false
    det397 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0358_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 130, 98, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0358_orbit
  simpa only [lower69] using h

theorem space0359_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 163, 67, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 26), (163, 266), (67, 112), (19, 446), (10, 113), (4, 16)]
    (codeMat 335) (codeMat 177) (codeMat 417) false
    det335 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0359_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 163, 67, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0359_orbit
  simpa only [lower69] using h

theorem space0360_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 129, 98, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 26), (129, 112), (98, 282), (19, 113), (10, 446), (4, 16)]
    (codeMat 271) (codeMat 106) (codeMat 396) false
    det271 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0360_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 129, 98, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0360_orbit
  simpa only [lower69] using h

theorem space0361_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 128, 96, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 352), (128, 1), (96, 363), (19, 113), (10, 446), (7, 16)]
    (codeMat 460) (codeMat 334) (codeMat 442) false
    det460 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0361_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 128, 96, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0361_orbit
  simpa only [lower69] using h

theorem space0362_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 130, 99, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 272), (130, 1), (99, 267), (19, 113), (10, 463), (7, 16)]
    (codeMat 461) (codeMat 331) (codeMat 410) false
    det461 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0362_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 130, 99, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0362_orbit
  simpa only [lower69] using h

theorem space0363_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 128, 98, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (128, 1), (98, 267), (19, 113), (10, 463), (7, 16)]
    (codeMat 396) (codeMat 331) (codeMat 410) false
    det396 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0363_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 98, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0363_orbit
  simpa only [lower69] using h

theorem space0364_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 162, 99, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 272), (162, 164), (99, 212), (19, 446), (10, 463), (6, 16)]
    (codeMat 334) (codeMat 473) (codeMat 409) false
    det334 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0364_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 162, 99, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0364_orbit
  simpa only [lower69] using h

theorem space0365_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 131, 98, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 11), (131, 112), (98, 267), (19, 113), (10, 463), (6, 16)]
    (codeMat 270) (codeMat 111) (codeMat 412) false
    det270 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0365_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 131, 98, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0365_orbit
  simpa only [lower69] using h

theorem space0366_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [262, 130, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(262, 100), (130, 9), (64, 40), (18, 54), (10, 52), (1, 32)]
    (codeMat 85) (codeMat 282) (codeMat 267) true
    det85 det282 inv282
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0366_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0366_orbit
  simpa only [lower31] using h

theorem space0367_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (134, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 177) (codeMat 417) false
    det428 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0367_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0367_orbit
  simpa only [lower144] using h

theorem space0368_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 101, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (131, 440), (101, 34), (19, 441), (10, 462)]
    (codeMat 302) (codeMat 106) (codeMat 396) false
    det302 det106 inv106
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0368_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 101, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0368_orbit
  simpa only [lower144] using h

theorem space0369_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 161, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (161, 84), (99, 492), (19, 119), (10, 462)]
    (codeMat 303) (codeMat 474) (codeMat 395) false
    det303 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0369_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0369_orbit
  simpa only [lower144] using h

theorem space0370_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [258, 194, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(258, 37), (194, 53), (19, 350), (10, 427), (6, 36)]
    (codeMat 485) (codeMat 206) (codeMat 498) false
    det485 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0370_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 194, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0370_orbit
  simpa only [lower220] using h

theorem space0371_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [323, 131, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(323, 37), (131, 53), (19, 245), (10, 427), (6, 36)]
    (codeMat 421) (codeMat 382) (codeMat 499) false
    det421 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0371_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 131, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0371_orbit
  simpa only [lower220] using h

theorem space0372_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 162, 65, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 368), (162, 362), (65, 1), (19, 463), (10, 113), (6, 16)]
    (codeMat 397) (codeMat 407) (codeMat 405) false
    det397 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0372_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 162, 65, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0372_orbit
  simpa only [lower69] using h

theorem space0373_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 163, 65, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 272), (163, 266), (65, 1), (19, 446), (10, 113), (6, 16)]
    (codeMat 461) (codeMat 401) (codeMat 401) false
    det461 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0373_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 163, 65, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0373_orbit
  simpa only [lower69] using h

theorem space0374_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [419, 99, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(419, 460), (99, 492), (19, 462), (10, 119), (6, 1)]
    (codeMat 305) (codeMat 395) (codeMat 474) true
    det305 det395 inv395
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0374_lower : 15 ≤ frozenWangTable.L0 (spanCodes [419, 99, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0374_orbit
  simpa only [lower144] using h

theorem space0375_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 161, 96, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 368), (161, 181), (96, 197), (19, 463), (10, 446), (6, 16)]
    (codeMat 270) (codeMat 478) (codeMat 445) false
    det270 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0375_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 161, 96, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0375_orbit
  simpa only [lower69] using h

theorem space0376_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 129, 97, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (129, 112), (97, 363), (19, 113), (10, 446), (6, 16)]
    (codeMat 271) (codeMat 110) (codeMat 444) false
    det271 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0376_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 129, 97, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0376_orbit
  simpa only [lower69] using h

theorem space0377_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 162, 64, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 272), (162, 283), (64, 1), (19, 463), (10, 113), (7, 16)]
    (codeMat 460) (codeMat 403) (codeMat 403) false
    det460 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0377_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 162, 64, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0377_orbit
  simpa only [lower69] using h

theorem space0378_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 163, 64, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 368), (163, 379), (64, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 396) (codeMat 405) (codeMat 407) false
    det396 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0378_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 163, 64, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0378_orbit
  simpa only [lower69] using h

theorem space0379_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 160, 65, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (160, 283), (65, 1), (19, 463), (10, 113), (7, 16)]
    (codeMat 397) (codeMat 403) (codeMat 403) false
    det397 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0379_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 65, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0379_orbit
  simpa only [lower69] using h

theorem space0380_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 161, 65, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 352), (161, 379), (65, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 461) (codeMat 405) (codeMat 407) false
    det461 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0380_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 161, 65, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0380_orbit
  simpa only [lower69] using h

theorem space0381_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 161, 66, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 10), (161, 266), (66, 112), (19, 446), (10, 113), (4, 16)]
    (codeMat 270) (codeMat 177) (codeMat 417) false
    det270 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0381_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 161, 66, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0381_orbit
  simpa only [lower69] using h

theorem space0382_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 131, 99, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 10), (131, 112), (99, 282), (19, 113), (10, 446), (4, 16)]
    (codeMat 334) (codeMat 106) (codeMat 396) false
    det334 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0382_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 131, 99, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0382_orbit
  simpa only [lower69] using h

theorem space0383_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 160, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (160, 283), (67, 112), (19, 463), (10, 113), (5, 16)]
    (codeMat 271) (codeMat 183) (codeMat 419) false
    det271 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0383_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0383_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
