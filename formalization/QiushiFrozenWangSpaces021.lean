import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0672_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 133, 68, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 353), (133, 378), (68, 180), (39, 97), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 474) (codeMat 395) false
    det478 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0672_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 68, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0672_orbit
  simpa only [lower69] using h

theorem space0673_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 132, 66, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (132, 283), (66, 447), (39, 430), (19, 113), (10, 446)]
    (codeMat 286) (codeMat 183) (codeMat 419) false
    det286 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0673_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 66, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0673_orbit
  simpa only [lower69] using h

theorem space0674_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 133, 64, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 223), (133, 362), (64, 1), (38, 479), (19, 113), (10, 446)]
    (codeMat 412) (codeMat 403) (codeMat 403) false
    det412 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0674_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 64, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0674_orbit
  simpa only [lower69] using h

theorem space0675_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 134, 64, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 257), (134, 197), (64, 1), (38, 430), (19, 113), (10, 463)]
    (codeMat 348) (codeMat 405) (codeMat 407) false
    det348 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0675_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 134, 64, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0675_orbit
  simpa only [lower69] using h

theorem space0676_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 132, 67, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (132, 283), (67, 447), (38, 479), (19, 113), (10, 446)]
    (codeMat 351) (codeMat 403) (codeMat 403) false
    det351 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0676_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 67, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0676_orbit
  simpa only [lower69] using h

theorem space0677_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 135, 67, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 175), (135, 180), (67, 462), (38, 430), (19, 113), (10, 463)]
    (codeMat 415) (codeMat 405) (codeMat 407) false
    det415 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0677_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 67, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0677_orbit
  simpa only [lower69] using h

theorem space0678_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 129, 69, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (129, 447), (69, 283), (33, 479), (19, 446), (10, 113)]
    (codeMat 279) (codeMat 331) (codeMat 410) false
    det279 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0678_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 69, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0678_orbit
  simpa only [lower69] using h

theorem space0679_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 130, 68, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 257), (130, 1), (68, 197), (33, 430), (19, 463), (10, 113)]
    (codeMat 277) (codeMat 334) (codeMat 442) false
    det277 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0679_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 68, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0679_orbit
  simpa only [lower69] using h

theorem space0680_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 130, 71, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 223), (130, 1), (71, 362), (33, 479), (19, 446), (10, 113)]
    (codeMat 405) (codeMat 331) (codeMat 410) false
    det405 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0680_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 71, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0680_orbit
  simpa only [lower69] using h

theorem space0681_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 129, 70, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 175), (129, 462), (70, 180), (33, 430), (19, 463), (10, 113)]
    (codeMat 407) (codeMat 334) (codeMat 442) false
    det407 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0681_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 70, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0681_orbit
  simpa only [lower69] using h

theorem space0682_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 128, 70, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 453), (128, 1), (70, 197), (32, 16), (19, 463), (10, 113)]
    (codeMat 340) (codeMat 106) (codeMat 396) false
    det340 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0682_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 70, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0682_orbit
  simpa only [lower69] using h

theorem space0683_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 135, 64, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 436), (135, 363), (64, 1), (32, 16), (19, 463), (10, 446)]
    (codeMat 468) (codeMat 177) (codeMat 417) false
    det468 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0683_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 64, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0683_orbit
  simpa only [lower69] using h

theorem space0684_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 131, 69, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (131, 447), (69, 283), (35, 430), (19, 446), (10, 113)]
    (codeMat 342) (codeMat 111) (codeMat 412) false
    det342 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0684_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 69, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0684_orbit
  simpa only [lower69] using h

theorem space0685_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 134, 71, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 353), (134, 180), (71, 378), (35, 97), (19, 113), (10, 446)]
    (codeMat 470) (codeMat 473) (codeMat 409) false
    det470 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0685_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 71, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0685_orbit
  simpa only [lower69] using h

theorem space0686_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [262, 193, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(262, 398), (193, 414), (34, 399), (19, 245), (10, 427)]
    (codeMat 431) (codeMat 213) (codeMat 470) false
    det431 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0686_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 193, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0686_orbit
  simpa only [lower220] using h

theorem space0687_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 135, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (135, 34), (34, 118), (19, 441), (10, 119)]
    (codeMat 354) (codeMat 339) (codeMat 467) true
    det354 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0687_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 135, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0687_orbit
  simpa only [lower144] using h

theorem space0688_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 129, 68, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 353), (129, 462), (68, 180), (34, 97), (19, 463), (10, 113)]
    (codeMat 407) (codeMat 330) (codeMat 394) false
    det407 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0688_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 68, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0688_orbit
  simpa only [lower69] using h

theorem space0689_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 129, 71, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 191), (129, 447), (71, 283), (34, 97), (19, 446), (10, 113)]
    (codeMat 279) (codeMat 335) (codeMat 426) false
    det279 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0689_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 71, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0689_orbit
  simpa only [lower69] using h

theorem space0690_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 134, 70, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 257), (134, 197), (70, 196), (34, 430), (19, 113), (10, 446)]
    (codeMat 340) (codeMat 477) (codeMat 431) false
    det340 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0690_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 70, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0690_orbit
  simpa only [lower69] using h

theorem space0691_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [391, 64, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(391, 208), (64, 192), (34, 399), (19, 350), (10, 427)]
    (codeMat 303) (codeMat 445) (codeMat 478) false
    det303 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0691_lower : 15 ≤ frozenWangTable.L0 (spanCodes [391, 64, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0691_orbit
  simpa only [lower220] using h

theorem space0692_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 163, 99, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 256), (163, 267), (99, 266), (19, 463), (10, 446), (5, 16)]
    (codeMat 396) (codeMat 474) (codeMat 395) false
    det396 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0692_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 163, 99, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0692_orbit
  simpa only [lower69] using h

theorem space0693_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 161, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 11), (161, 212), (64, 1), (19, 463), (10, 113), (5, 16)]
    (codeMat 460) (codeMat 183) (codeMat 419) false
    det460 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0693_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 161, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0693_orbit
  simpa only [lower69] using h

theorem space0694_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 225, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (225, 85), (19, 441), (10, 462), (4, 1)]
    (codeMat 417) (codeMat 213) (codeMat 470) true
    det417 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0694_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 225, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0694_orbit
  simpa only [lower144] using h

theorem space0695_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [355, 130, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(355, 379), (130, 192), (19, 245), (10, 350), (4, 36)]
    (codeMat 375) (codeMat 339) (codeMat 467) false
    det375 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0695_lower : 15 ≤ frozenWangTable.L0 (spanCodes [355, 130, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0695_orbit
  simpa only [lower220] using h

theorem space0696_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 163, 97, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 26), (163, 282), (97, 362), (19, 446), (10, 463), (4, 16)]
    (codeMat 271) (codeMat 249) (codeMat 425) false
    det271 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0696_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 163, 97, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0696_orbit
  simpa only [lower69] using h

theorem space0697_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 128, 99, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 10), (128, 1), (99, 181), (19, 113), (10, 463), (4, 16)]
    (codeMat 396) (codeMat 107) (codeMat 428) false
    det396 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0697_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 99, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0697_orbit
  simpa only [lower69] using h

theorem space0698_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 160, 98, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 26), (160, 378), (98, 266), (19, 463), (10, 446), (4, 16)]
    (codeMat 335) (codeMat 250) (codeMat 397) false
    det335 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0698_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 160, 98, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0698_orbit
  simpa only [lower69] using h

theorem space0699_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 161, 65, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 26), (161, 165), (65, 1), (19, 463), (10, 113), (4, 16)]
    (codeMat 397) (codeMat 179) (codeMat 421) false
    det397 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0699_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 161, 65, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0699_orbit
  simpa only [lower69] using h

theorem space0700_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [417, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(417, 379), (64, 192), (19, 350), (10, 245), (4, 36)]
    (codeMat 311) (codeMat 395) (codeMat 474) false
    det311 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0700_lower : 15 ≤ frozenWangTable.L0 (spanCodes [417, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0700_orbit
  simpa only [lower220] using h

theorem space0701_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 160, 97, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 11), (160, 363), (97, 283), (19, 446), (10, 463), (7, 16)]
    (codeMat 334) (codeMat 253) (codeMat 415) false
    det334 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0701_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 160, 97, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0701_orbit
  simpa only [lower69] using h

theorem space0702_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 162, 96, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (162, 363), (96, 283), (19, 446), (10, 463), (7, 16)]
    (codeMat 271) (codeMat 253) (codeMat 415) false
    det271 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0702_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 162, 96, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0702_orbit
  simpa only [lower69] using h

theorem space0703_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 161, 99, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (161, 267), (99, 379), (19, 463), (10, 446), (7, 16)]
    (codeMat 335) (codeMat 254) (codeMat 443) false
    det335 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0703_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 161, 99, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0703_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
