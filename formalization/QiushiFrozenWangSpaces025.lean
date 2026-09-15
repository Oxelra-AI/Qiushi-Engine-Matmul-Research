import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0800_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 97, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 32), (97, 411), (19, 462), (10, 119), (7, 1)]
    (codeMat 305) (codeMat 431) (codeMat 477) true
    det305 det431 inv431
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0800_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 97, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space0800_orbit
  simpa only [lower144] using h

theorem space0801_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 226, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (226, 84), (19, 462), (10, 441), (4, 1)]
    (codeMat 481) (codeMat 206) (codeMat 498) true
    det481 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0801_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 226, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0801_orbit
  simpa only [lower144] using h

theorem space0802_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [354, 128, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(354, 443), (128, 192), (19, 245), (10, 427), (4, 36)]
    (codeMat 311) (codeMat 346) (codeMat 459) false
    det311 det346 inv346
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0802_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 128, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0802_orbit
  simpa only [lower220] using h

theorem space0803_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 130, 98, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 26), (130, 1), (98, 181), (19, 113), (10, 463), (4, 16)]
    (codeMat 461) (codeMat 107) (codeMat 428) false
    det461 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0803_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 98, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0803_orbit
  simpa only [lower69] using h

theorem space0804_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 162, 99, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 10), (162, 378), (99, 266), (19, 463), (10, 446), (4, 16)]
    (codeMat 270) (codeMat 250) (codeMat 397) false
    det270 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0804_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 162, 99, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0804_orbit
  simpa only [lower69] using h

theorem space0805_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 161, 96, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 10), (161, 282), (96, 362), (19, 446), (10, 463), (4, 16)]
    (codeMat 334) (codeMat 249) (codeMat 425) false
    det334 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0805_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 161, 96, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0805_orbit
  simpa only [lower69] using h

theorem space0806_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 163, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 10), (163, 165), (64, 1), (19, 463), (10, 113), (4, 16)]
    (codeMat 460) (codeMat 179) (codeMat 421) false
    det460 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0806_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 163, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0806_orbit
  simpa only [lower69] using h

theorem space0807_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [419, 65, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(419, 443), (65, 192), (19, 427), (10, 245), (4, 36)]
    (codeMat 375) (codeMat 409) (codeMat 473) false
    det375 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0807_lower : 15 ≤ frozenWangTable.L0 (spanCodes [419, 65, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0807_orbit
  simpa only [lower220] using h

theorem space0808_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 195, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (195, 192), (19, 350), (10, 427), (5, 36)]
    (codeMat 375) (codeMat 234) (codeMat 461) false
    det375 det234 inv234
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0808_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 195, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0808_orbit
  simpa only [lower220] using h

theorem space0809_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 163, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 2), (163, 410), (19, 119), (10, 462), (5, 1)]
    (codeMat 481) (codeMat 339) (codeMat 467) true
    det481 det339 inv339
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0809_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 163, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 144 space0809_orbit
  simpa only [lower144] using h

theorem space0810_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 131, 99, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 368), (131, 112), (99, 181), (19, 113), (10, 463), (5, 16)]
    (codeMat 270) (codeMat 335) (codeMat 426) false
    det270 det335 inv335
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0810_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 99, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0810_orbit
  simpa only [lower69] using h

theorem space0811_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [291, 160, 96, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(291, 352), (160, 363), (96, 362), (19, 446), (10, 463), (5, 16)]
    (codeMat 460) (codeMat 477) (codeMat 431) false
    det460 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0811_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 160, 96, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0811_orbit
  simpa only [lower69] using h

theorem space0812_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 131, 97, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 272), (131, 112), (97, 164), (19, 113), (10, 446), (5, 16)]
    (codeMat 334) (codeMat 330) (codeMat 394) false
    det334 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0812_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 97, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0812_orbit
  simpa only [lower69] using h

theorem space0813_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [419, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(419, 334), (64, 192), (19, 350), (10, 245), (5, 36)]
    (codeMat 311) (codeMat 431) (codeMat 477) false
    det311 det431 inv431
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0813_lower : 15 ≤ frozenWangTable.L0 (spanCodes [419, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 220 space0813_orbit
  simpa only [lower220] using h

theorem space0814_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 162, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (162, 197), (65, 1), (19, 446), (10, 113), (5, 16)]
    (codeMat 461) (codeMat 181) (codeMat 423) false
    det461 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0814_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 162, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0814_orbit
  simpa only [lower69] using h

theorem space0815_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (128, 1), (103, 410), (19, 462), (10, 441)]
    (codeMat 380) (codeMat 111) (codeMat 412) false
    det380 det111 inv111
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0815_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0815_orbit
  simpa only [lower144] using h

theorem space0816_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 162, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (162, 34), (97, 35), (19, 119), (10, 441)]
    (codeMat 317) (codeMat 473) (codeMat 409) false
    det317 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0816_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0816_orbit
  simpa only [lower144] using h

theorem space0817_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 133, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (133, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 177) (codeMat 417) false
    det318 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0817_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0817_orbit
  simpa only [lower144] using h

theorem space0818_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 195, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 208), (195, 192), (39, 209), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 213) (codeMat 470) false
    det359 det213 inv213
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0818_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 195, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0818_orbit
  simpa only [lower220] using h

theorem space0819_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 135, 70, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 191), (135, 164), (70, 283), (39, 97), (19, 463), (10, 113)]
    (codeMat 286) (codeMat 477) (codeMat 431) false
    det286 det477 inv477
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0819_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 70, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0819_orbit
  simpa only [lower69] using h

theorem space0820_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 129, 69, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (129, 447), (69, 164), (39, 479), (19, 446), (10, 463)]
    (codeMat 351) (codeMat 330) (codeMat 394) false
    det351 det330 inv330
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0820_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 129, 69, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0820_orbit
  simpa only [lower69] using h

theorem space0821_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [386, 66, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(386, 398), (66, 414), (39, 378), (19, 245), (10, 350)]
    (codeMat 423) (codeMat 445) (codeMat 478) false
    det423 det445 inv445
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0821_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 66, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0821_orbit
  simpa only [lower220] using h

theorem space0822_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 134, 65, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 452), (134, 197), (65, 1), (39, 479), (19, 113), (10, 463)]
    (codeMat 285) (codeMat 181) (codeMat 423) false
    det285 det181 inv181
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0822_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 65, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0822_orbit
  simpa only [lower69] using h

theorem space0823_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 129, 71, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 191), (129, 447), (71, 164), (38, 97), (19, 446), (10, 463)]
    (codeMat 351) (codeMat 334) (codeMat 442) false
    det351 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0823_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 71, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0823_orbit
  simpa only [lower69] using h

theorem space0824_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 129, 70, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 353), (129, 462), (70, 378), (38, 97), (19, 463), (10, 446)]
    (codeMat 415) (codeMat 331) (codeMat 410) false
    det415 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0824_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 129, 70, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0824_orbit
  simpa only [lower69] using h

theorem space0825_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 128, 69, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (128, 1), (69, 196), (38, 97), (19, 463), (10, 446)]
    (codeMat 348) (codeMat 331) (codeMat 410) false
    det348 det331 inv331
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0825_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 69, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0825_orbit
  simpa only [lower69] using h

theorem space0826_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 128, 68, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 222), (128, 1), (68, 363), (38, 97), (19, 446), (10, 463)]
    (codeMat 412) (codeMat 334) (codeMat 442) false
    det412 det334 inv334
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0826_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 68, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0826_orbit
  simpa only [lower69] using h

theorem space0827_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 133, 70, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 223), (133, 363), (70, 362), (37, 479), (19, 463), (10, 113)]
    (codeMat 477) (codeMat 473) (codeMat 409) false
    det477 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0827_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 133, 70, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0827_orbit
  simpa only [lower69] using h

theorem space0828_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 130, 69, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 452), (130, 1), (69, 196), (37, 479), (19, 463), (10, 446)]
    (codeMat 285) (codeMat 111) (codeMat 412) false
    det285 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0828_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 130, 69, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0828_orbit
  simpa only [lower69] using h

theorem space0829_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 131, 69, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 420), (131, 447), (69, 164), (36, 16), (19, 446), (10, 463)]
    (codeMat 286) (codeMat 106) (codeMat 396) false
    det286 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0829_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 131, 69, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0829_orbit
  simpa only [lower69] using h

theorem space0830_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 134, 66, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 469), (134, 180), (66, 462), (36, 16), (19, 113), (10, 463)]
    (codeMat 478) (codeMat 177) (codeMat 417) false
    det478 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0830_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 134, 66, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0830_orbit
  simpa only [lower69] using h

theorem space0831_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 128, 71, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 437), (128, 1), (71, 362), (35, 430), (19, 446), (10, 113)]
    (codeMat 468) (codeMat 111) (codeMat 412) false
    det468 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0831_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 71, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0831_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
