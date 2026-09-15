import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0608_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [326, 129, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(326, 398), (129, 414), (36, 36), (19, 350), (10, 427)]
    (codeMat 494) (codeMat 339) (codeMat 467) false
    det494 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0608_lower : 15 ≤ frozenWangTable.L0 (spanCodes [326, 129, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0608_orbit
  simpa only [lower220] using h

theorem space0609_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 135, 67, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 420), (135, 283), (67, 447), (36, 16), (19, 113), (10, 446)]
    (codeMat 351) (codeMat 179) (codeMat 421) false
    det351 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0609_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 67, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0609_orbit
  simpa only [lower69] using h

theorem space0610_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [391, 64, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(391, 208), (64, 192), (36, 36), (19, 245), (10, 427)]
    (codeMat 302) (codeMat 395) (codeMat 474) false
    det302 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0610_lower : 15 ≤ frozenWangTable.L0 (spanCodes [391, 64, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0610_orbit
  simpa only [lower220] using h

theorem space0611_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 134, 71, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 420), (134, 164), (71, 283), (36, 16), (19, 463), (10, 113)]
    (codeMat 286) (codeMat 249) (codeMat 425) false
    det286 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0611_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 71, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0611_orbit
  simpa only [lower69] using h

theorem space0612_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 128, 70, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 453), (128, 1), (70, 196), (36, 16), (19, 463), (10, 446)]
    (codeMat 348) (codeMat 107) (codeMat 428) false
    det348 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0612_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 70, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0612_orbit
  simpa only [lower69] using h

theorem space0613_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 132, 69, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 469), (132, 378), (69, 180), (36, 16), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 250) (codeMat 397) false
    det478 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0613_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 132, 69, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0613_orbit
  simpa only [lower69] using h

theorem space0614_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [289, 128, 65, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(289, 100), (128, 3), (65, 63), (16, 2), (9, 54), (3, 32)]
    (codeMat 86) (codeMat 267) (codeMat 282) true
    det86 det267 inv267
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0614_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 128, 65, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0614_orbit
  simpa only [lower31] using h

theorem space0615_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [290, 130, 66, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(290, 100), (130, 63), (66, 60), (18, 54), (10, 52), (1, 32)]
    (codeMat 86) (codeMat 282) (codeMat 267) true
    det86 det282 inv282
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0615_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 130, 66, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0615_orbit
  simpa only [lower31] using h

theorem space0616_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 164, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 32), (164, 35), (100, 34), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 474) (codeMat 395) false
    det380 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0616_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0616_orbit
  simpa only [lower144] using h

theorem space0617_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 71, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (131, 118), (71, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 111) (codeMat 412) false
    det318 det111 inv111
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0617_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 71, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0617_orbit
  simpa only [lower144] using h

theorem space0618_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 161, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (161, 410), (65, 1), (19, 441), (10, 462)]
    (codeMat 317) (codeMat 183) (codeMat 419) false
    det317 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0618_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0618_orbit
  simpa only [lower144] using h

theorem space0619_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (196, 34), (36, 1), (19, 462), (10, 119)]
    (codeMat 299) (codeMat 213) (codeMat 470) true
    det299 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0619_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0619_orbit
  simpa only [lower144] using h

theorem space0620_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [323, 131, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(323, 398), (131, 414), (36, 36), (19, 350), (10, 427)]
    (codeMat 423) (codeMat 339) (codeMat 467) false
    det423 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0620_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 131, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0620_orbit
  simpa only [lower220] using h

theorem space0621_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 68, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 469), (134, 378), (68, 180), (36, 16), (19, 446), (10, 113)]
    (codeMat 415) (codeMat 250) (codeMat 397) false
    det415 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0621_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 68, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0621_orbit
  simpa only [lower69] using h

theorem space0622_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 132, 70, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 420), (132, 164), (70, 283), (36, 16), (19, 463), (10, 113)]
    (codeMat 351) (codeMat 249) (codeMat 425) false
    det351 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0622_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 70, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0622_orbit
  simpa only [lower69] using h

theorem space0623_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [385, 65, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(385, 208), (65, 192), (36, 36), (19, 245), (10, 427)]
    (codeMat 359) (codeMat 395) (codeMat 474) false
    det359 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0623_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 65, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0623_orbit
  simpa only [lower220] using h

theorem space0624_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 133, 66, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 420), (133, 283), (66, 447), (36, 16), (19, 113), (10, 446)]
    (codeMat 286) (codeMat 179) (codeMat 421) false
    det286 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0624_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 66, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0624_orbit
  simpa only [lower69] using h

theorem space0625_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 132, 69, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (132, 164), (69, 283), (37, 479), (19, 463), (10, 113)]
    (codeMat 286) (codeMat 473) (codeMat 409) false
    det286 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0625_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 69, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0625_orbit
  simpa only [lower69] using h

theorem space0626_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 131, 70, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (131, 462), (70, 378), (37, 479), (19, 463), (10, 446)]
    (codeMat 478) (codeMat 111) (codeMat 412) false
    det478 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0626_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 131, 70, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0626_orbit
  simpa only [lower69] using h

theorem space0627_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 132, 68, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 452), (132, 196), (68, 197), (38, 479), (19, 446), (10, 113)]
    (codeMat 348) (codeMat 254) (codeMat 443) false
    det348 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0627_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 68, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0627_orbit
  simpa only [lower69] using h

theorem space0628_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 135, 69, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (135, 164), (69, 283), (38, 430), (19, 463), (10, 113)]
    (codeMat 351) (codeMat 253) (codeMat 415) false
    det351 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0628_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 69, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0628_orbit
  simpa only [lower69] using h

theorem space0629_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 70, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 437), (134, 363), (70, 362), (38, 430), (19, 463), (10, 113)]
    (codeMat 412) (codeMat 253) (codeMat 415) false
    det412 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0629_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 70, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0629_orbit
  simpa only [lower69] using h

theorem space0630_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 133, 71, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (133, 378), (71, 180), (38, 479), (19, 446), (10, 113)]
    (codeMat 415) (codeMat 254) (codeMat 443) false
    det415 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0630_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 71, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0630_orbit
  simpa only [lower69] using h

theorem space0631_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 132, 71, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (132, 196), (71, 197), (39, 97), (19, 446), (10, 113)]
    (codeMat 285) (codeMat 474) (codeMat 395) false
    det285 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0631_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 71, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0631_orbit
  simpa only [lower69] using h

theorem space0632_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [263, 133, 65, 39, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(263, 437), (133, 362), (65, 1), (39, 430), (19, 113), (10, 446)]
    (codeMat 477) (codeMat 183) (codeMat 419) false
    det477 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0632_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 65, 39, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0632_orbit
  simpa only [lower69] using h

theorem space0633_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 131, 68, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 469), (131, 462), (68, 180), (32, 16), (19, 463), (10, 113)]
    (codeMat 470) (codeMat 106) (codeMat 396) false
    det470 det106 inv106
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0633_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 68, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0633_orbit
  simpa only [lower69] using h

theorem space0634_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 132, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 420), (132, 164), (66, 447), (32, 16), (19, 463), (10, 446)]
    (codeMat 342) (codeMat 177) (codeMat 417) false
    det342 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0634_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0634_orbit
  simpa only [lower69] using h

theorem space0635_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 132, 65, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (132, 196), (65, 1), (33, 97), (19, 446), (10, 463)]
    (codeMat 277) (codeMat 403) (codeMat 403) false
    det277 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0635_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 65, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0635_orbit
  simpa only [lower69] using h

theorem space0636_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 134, 65, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 222), (134, 363), (65, 1), (33, 97), (19, 463), (10, 446)]
    (codeMat 405) (codeMat 405) (codeMat 407) false
    det405 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0636_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 134, 65, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0636_orbit
  simpa only [lower69] using h

theorem space0637_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 133, 67, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 191), (133, 164), (67, 447), (33, 97), (19, 463), (10, 446)]
    (codeMat 279) (codeMat 405) (codeMat 407) false
    det279 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0637_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 133, 67, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0637_orbit
  simpa only [lower69] using h

theorem space0638_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 135, 67, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 353), (135, 378), (67, 462), (33, 97), (19, 446), (10, 463)]
    (codeMat 407) (codeMat 403) (codeMat 403) false
    det407 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0638_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 67, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0638_orbit
  simpa only [lower69] using h

theorem space0639_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [262, 135, 71, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(262, 223), (135, 362), (71, 363), (34, 479), (19, 113), (10, 463)]
    (codeMat 468) (codeMat 474) (codeMat 395) false
    det468 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0639_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 71, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0639_orbit
  simpa only [lower69] using h


end QiushiMatmul.FrozenWang
