import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0640_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 132, 64, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 452), (132, 196), (64, 1), (34, 479), (19, 446), (10, 463)]
    (codeMat 340) (codeMat 183) (codeMat 419) false
    det340 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0640_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 64, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0640_orbit
  simpa only [lower69] using h

theorem space0641_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [263, 192, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(263, 208), (192, 192), (35, 209), (19, 245), (10, 350)]
    (codeMat 303) (codeMat 206) (codeMat 498) false
    det303 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0641_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 192, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0641_orbit
  simpa only [lower220] using h

theorem space0642_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [324, 131, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(324, 398), (131, 414), (35, 378), (19, 350), (10, 245)]
    (codeMat 431) (codeMat 382) (codeMat 499) false
    det431 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0642_lower : 15 ≤ frozenWangTable.L0 (spanCodes [324, 131, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0642_orbit
  simpa only [lower220] using h

theorem space0643_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 128, 68, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 452), (128, 1), (68, 197), (35, 479), (19, 463), (10, 113)]
    (codeMat 340) (codeMat 110) (codeMat 444) false
    det340 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0643_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 68, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0643_orbit
  simpa only [lower69] using h

theorem space0644_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 135, 70, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 191), (135, 283), (70, 164), (35, 97), (19, 113), (10, 463)]
    (codeMat 342) (codeMat 478) (codeMat 445) false
    det342 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0644_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 70, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0644_orbit
  simpa only [lower69] using h

theorem space0645_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 71, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 2), (71, 34), (35, 463), (19, 462), (10, 441)]
    (codeMat 354) (codeMat 445) (codeMat 478) true
    det354 det445 inv445
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0645_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 71, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0645_orbit
  simpa only [lower144] using h

theorem space0646_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 67, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 175), (134, 378), (67, 462), (35, 430), (19, 446), (10, 463)]
    (codeMat 407) (codeMat 407) (codeMat 405) false
    det407 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0646_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 67, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0646_orbit
  simpa only [lower69] using h

theorem space0647_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 130, 96, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 26), (130, 1), (96, 164), (19, 113), (10, 446), (4, 16)]
    (codeMat 397) (codeMat 106) (codeMat 396) false
    det397 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0647_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 96, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0647_orbit
  simpa only [lower69] using h

theorem space0648_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 160, 65, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 26), (160, 180), (65, 1), (19, 446), (10, 113), (4, 16)]
    (codeMat 461) (codeMat 177) (codeMat 417) false
    det461 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0648_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 160, 65, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0648_orbit
  simpa only [lower69] using h

theorem space0649_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [289, 192, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(289, 37), (192, 192), (19, 427), (10, 350), (5, 36)]
    (codeMat 311) (codeMat 213) (codeMat 470) false
    det311 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0649_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 192, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0649_orbit
  simpa only [lower220] using h

theorem space0650_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 161, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (161, 492), (19, 119), (10, 441), (5, 1)]
    (codeMat 417) (codeMat 382) (codeMat 499) true
    det417 det382 inv382
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0650_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 161, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0650_orbit
  simpa only [lower144] using h

theorem space0651_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 129, 96, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (129, 112), (96, 164), (19, 113), (10, 446), (5, 16)]
    (codeMat 271) (codeMat 330) (codeMat 394) false
    det271 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0651_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 96, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0651_orbit
  simpa only [lower69] using h

theorem space0652_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 162, 97, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 368), (162, 363), (97, 362), (19, 446), (10, 463), (5, 16)]
    (codeMat 397) (codeMat 477) (codeMat 431) false
    det397 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0652_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 162, 97, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0652_orbit
  simpa only [lower69] using h

theorem space0653_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 129, 98, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 352), (129, 112), (98, 181), (19, 113), (10, 463), (5, 16)]
    (codeMat 335) (codeMat 335) (codeMat 426) false
    det335 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0653_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 98, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0653_orbit
  simpa only [lower69] using h

theorem space0654_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 160, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 11), (160, 197), (64, 1), (19, 446), (10, 113), (5, 16)]
    (codeMat 396) (codeMat 181) (codeMat 423) false
    det396 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0654_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 160, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0654_orbit
  simpa only [lower69] using h

theorem space0655_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [416, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(416, 398), (65, 192), (19, 427), (10, 245), (5, 36)]
    (codeMat 375) (codeMat 445) (codeMat 478) false
    det375 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0655_lower : 15 ≤ frozenWangTable.L0 (spanCodes [416, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0655_orbit
  simpa only [lower220] using h

theorem space0656_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 128, 96, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 11), (128, 1), (96, 196), (19, 113), (10, 463), (6, 16)]
    (codeMat 396) (codeMat 111) (codeMat 412) false
    det396 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0656_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 96, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0656_orbit
  simpa only [lower69] using h

theorem space0657_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 161, 97, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 272), (161, 282), (97, 283), (19, 446), (10, 463), (6, 16)]
    (codeMat 460) (codeMat 473) (codeMat 409) false
    det460 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0657_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 161, 97, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0657_orbit
  simpa only [lower69] using h

theorem space0658_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 131, 96, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (131, 112), (96, 196), (19, 113), (10, 463), (7, 16)]
    (codeMat 270) (codeMat 331) (codeMat 410) false
    det270 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0658_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 96, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0658_orbit
  simpa only [lower69] using h

theorem space0659_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 129, 97, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 272), (129, 112), (97, 196), (19, 113), (10, 463), (7, 16)]
    (codeMat 335) (codeMat 331) (codeMat 410) false
    det335 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0659_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 97, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0659_orbit
  simpa only [lower69] using h

theorem space0660_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 131, 98, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 352), (131, 112), (98, 213), (19, 113), (10, 446), (7, 16)]
    (codeMat 334) (codeMat 334) (codeMat 442) false
    det334 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0660_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 98, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0660_orbit
  simpa only [lower69] using h

theorem space0661_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 129, 99, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 368), (129, 112), (99, 213), (19, 113), (10, 446), (7, 16)]
    (codeMat 271) (codeMat 334) (codeMat 442) false
    det271 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0661_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 99, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0661_orbit
  simpa only [lower69] using h

theorem space0662_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 130, 99, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (130, 1), (99, 85), (19, 462), (10, 119)]
    (codeMat 317) (codeMat 106) (codeMat 396) false
    det317 det106 inv106
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0662_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 99, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0662_orbit
  simpa only [lower144] using h

theorem space0663_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 135, 70, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (135, 493), (70, 411), (19, 462), (10, 441)]
    (codeMat 318) (codeMat 474) (codeMat 395) false
    det318 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0663_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 135, 70, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0663_orbit
  simpa only [lower144] using h

theorem space0664_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 165, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (165, 85), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 177) (codeMat 417) false
    det380 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0664_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 165, 64, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0664_orbit
  simpa only [lower144] using h

theorem space0665_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [257, 193, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(257, 398), (193, 414), (37, 399), (19, 427), (10, 245)]
    (codeMat 423) (codeMat 206) (codeMat 498) false
    det423 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0665_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 193, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0665_orbit
  simpa only [lower220] using h

theorem space0666_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [322, 130, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(322, 208), (130, 192), (37, 399), (19, 427), (10, 350)]
    (codeMat 359) (codeMat 382) (codeMat 499) false
    det359 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0666_lower : 15 ≤ frozenWangTable.L0 (spanCodes [322, 130, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0666_orbit
  simpa only [lower220] using h

theorem space0667_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 135, 68, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 257), (135, 196), (68, 197), (37, 430), (19, 446), (10, 113)]
    (codeMat 285) (codeMat 478) (codeMat 445) false
    det285 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0667_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 68, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0667_orbit
  simpa only [lower69] using h

theorem space0668_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 131, 71, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (131, 447), (71, 164), (37, 430), (19, 446), (10, 463)]
    (codeMat 286) (codeMat 110) (codeMat 444) false
    det286 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0668_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 71, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0668_orbit
  simpa only [lower69] using h

theorem space0669_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 133, 67, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 191), (133, 283), (67, 447), (37, 97), (19, 113), (10, 446)]
    (codeMat 351) (codeMat 407) (codeMat 405) false
    det351 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0669_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 67, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0669_orbit
  simpa only [lower69] using h

theorem space0670_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 134, 67, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 353), (134, 180), (67, 462), (37, 97), (19, 113), (10, 463)]
    (codeMat 415) (codeMat 401) (codeMat 401) false
    det415 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0670_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 134, 67, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0670_orbit
  simpa only [lower69] using h

theorem space0671_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 135, 65, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 453), (135, 197), (65, 1), (36, 16), (19, 113), (10, 463)]
    (codeMat 285) (codeMat 177) (codeMat 417) false
    det285 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0671_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 65, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0671_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
