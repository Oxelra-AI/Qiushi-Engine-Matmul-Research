import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0832_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 133, 69, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (133, 197), (69, 196), (35, 97), (19, 113), (10, 446)]
    (codeMat 340) (codeMat 473) (codeMat 409) false
    det340 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0832_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 69, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0832_orbit
  simpa only [lower69] using h

theorem space0833_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 132, 69, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 256), (132, 283), (69, 164), (34, 479), (19, 113), (10, 463)]
    (codeMat 342) (codeMat 474) (codeMat 395) false
    det342 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0833_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0833_orbit
  simpa only [lower69] using h

theorem space0834_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 135, 66, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (135, 378), (66, 462), (34, 479), (19, 446), (10, 463)]
    (codeMat 470) (codeMat 183) (codeMat 419) false
    det470 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0834_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 66, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0834_orbit
  simpa only [lower69] using h

theorem space0835_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [260, 132, 70, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(260, 27), (132, 283), (70, 164), (33, 430), (19, 113), (10, 463)]
    (codeMat 279) (codeMat 254) (codeMat 443) false
    det279 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0835_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 70, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0835_orbit
  simpa only [lower69] using h

theorem space0836_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 134, 69, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 452), (134, 197), (69, 196), (33, 479), (19, 113), (10, 446)]
    (codeMat 277) (codeMat 253) (codeMat 415) false
    det277 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0836_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 134, 69, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0836_orbit
  simpa only [lower69] using h

theorem space0837_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 135, 68, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 437), (135, 362), (68, 363), (33, 430), (19, 113), (10, 463)]
    (codeMat 405) (codeMat 254) (codeMat 443) false
    det405 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0837_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 68, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0837_orbit
  simpa only [lower69] using h

theorem space0838_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 199, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 2), (199, 34), (32, 1), (19, 119), (10, 462)]
    (codeMat 354) (codeMat 206) (codeMat 498) true
    det354 det206 inv206
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0838_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 199, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0838_orbit
  simpa only [lower144] using h

theorem space0839_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [327, 128, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(327, 208), (128, 192), (32, 36), (19, 427), (10, 245)]
    (codeMat 303) (codeMat 339) (codeMat 467) false
    det303 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0839_lower : 15 ≤ frozenWangTable.L0 (spanCodes [327, 128, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0839_orbit
  simpa only [lower220] using h

theorem space0840_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 131, 71, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 420), (131, 447), (71, 283), (32, 16), (19, 446), (10, 113)]
    (codeMat 342) (codeMat 107) (codeMat 428) false
    det342 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0840_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 71, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0840_orbit
  simpa only [lower69] using h

theorem space0841_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 135, 69, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 420), (135, 283), (69, 164), (32, 16), (19, 113), (10, 463)]
    (codeMat 279) (codeMat 250) (codeMat 397) false
    det279 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0841_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 135, 69, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0841_orbit
  simpa only [lower69] using h

theorem space0842_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [261, 134, 68, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(261, 469), (134, 180), (68, 378), (32, 16), (19, 113), (10, 446)]
    (codeMat 407) (codeMat 249) (codeMat 425) false
    det407 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0842_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 134, 68, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0842_orbit
  simpa only [lower69] using h

theorem space0843_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [389, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(389, 398), (66, 414), (32, 36), (19, 427), (10, 350)]
    (codeMat 431) (codeMat 395) (codeMat 474) false
    det431 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0843_lower : 15 ≤ frozenWangTable.L0 (spanCodes [389, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 220 space0843_orbit
  simpa only [lower220] using h

theorem space0844_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 133, 64, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 453), (133, 196), (64, 1), (32, 16), (19, 446), (10, 463)]
    (codeMat 340) (codeMat 179) (codeMat 421) false
    det340 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0844_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 64, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space0844_orbit
  simpa only [lower69] using h

theorem space0845_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 163, 67, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (163, 212), (67, 112), (19, 463), (10, 113), (7, 16)]
    (codeMat 271) (codeMat 403) (codeMat 403) false
    det271 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0845_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 67, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0845_orbit
  simpa only [lower69] using h

theorem space0846_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 161, 66, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 272), (161, 212), (66, 112), (19, 463), (10, 113), (7, 16)]
    (codeMat 334) (codeMat 403) (codeMat 403) false
    det334 det403 inv403
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0846_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 161, 66, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0846_orbit
  simpa only [lower69] using h

theorem space0847_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 160, 66, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 368), (160, 197), (66, 112), (19, 446), (10, 113), (7, 16)]
    (codeMat 270) (codeMat 405) (codeMat 407) false
    det270 det405 inv405
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0847_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 160, 66, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0847_orbit
  simpa only [lower69] using h

theorem space0848_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [290, 195, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(290, 37), (195, 192), (19, 350), (10, 427), (6, 36)]
    (codeMat 375) (codeMat 206) (codeMat 498) false
    det375 det206 inv206
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0848_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 195, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0848_orbit
  simpa only [lower220] using h

theorem space0849_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [353, 128, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(353, 398), (128, 192), (19, 245), (10, 427), (6, 36)]
    (codeMat 311) (codeMat 382) (codeMat 499) false
    det311 det382 inv382
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0849_lower : 15 ≤ frozenWangTable.L0 (spanCodes [353, 128, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space0849_orbit
  simpa only [lower220] using h

theorem space0850_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 130, 99, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (130, 1), (99, 213), (19, 113), (10, 446), (6, 16)]
    (codeMat 397) (codeMat 110) (codeMat 444) false
    det397 det110 inv110
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0850_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 99, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0850_orbit
  simpa only [lower69] using h

theorem space0851_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 162, 98, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 368), (162, 378), (98, 379), (19, 463), (10, 446), (6, 16)]
    (codeMat 396) (codeMat 478) (codeMat 445) false
    det396 det478 inv478
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0851_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 162, 98, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0851_orbit
  simpa only [lower69] using h

theorem space0852_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [384, 97, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(384, 2), (97, 411), (19, 462), (10, 119), (6, 1)]
    (codeMat 417) (codeMat 395) (codeMat 474) true
    det417 det395 inv395
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0852_lower : 15 ≤ frozenWangTable.L0 (spanCodes [384, 97, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 144 space0852_orbit
  simpa only [lower144] using h

theorem space0853_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 161, 67, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 368), (161, 165), (67, 112), (19, 463), (10, 113), (6, 16)]
    (codeMat 271) (codeMat 407) (codeMat 405) false
    det271 det407 inv407
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0853_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 161, 67, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0853_orbit
  simpa only [lower69] using h

theorem space0854_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [258, 160, 67, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(258, 272), (160, 180), (67, 112), (19, 446), (10, 113), (6, 16)]
    (codeMat 335) (codeMat 401) (codeMat 401) false
    det335 det401 inv401
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0854_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 160, 67, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0854_orbit
  simpa only [lower69] using h

theorem space0855_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 161, 98, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 272), (161, 267), (98, 266), (19, 463), (10, 446), (5, 16)]
    (codeMat 461) (codeMat 474) (codeMat 395) false
    det461 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0855_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 161, 98, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0855_orbit
  simpa only [lower69] using h

theorem space0856_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 163, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (163, 212), (65, 1), (19, 463), (10, 113), (5, 16)]
    (codeMat 397) (codeMat 183) (codeMat 419) false
    det397 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0856_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0856_orbit
  simpa only [lower69] using h

theorem space0857_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [257, 162, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(257, 10), (162, 180), (64, 1), (19, 446), (10, 113), (4, 16)]
    (codeMat 396) (codeMat 177) (codeMat 417) false
    det396 det177 inv177
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0857_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 162, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0857_orbit
  simpa only [lower69] using h

theorem space0858_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [293, 129, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(293, 100), (129, 35), (64, 63), (16, 2), (9, 54), (3, 32)]
    (codeMat 87) (codeMat 267) (codeMat 282) true
    det87 det267 inv267
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0858_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 129, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0858_orbit
  simpa only [lower31] using h

theorem space0859_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [449, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(449, 120), (33, 60), (16, 2), (9, 63), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 345) (codeMat 345) false
    det266 det345 inv345
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0859_lower : 15 ≤ frozenWangTable.L0 (spanCodes [449, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0859_orbit
  simpa only [lower31] using h

theorem space0860_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [293, 129, 65, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(293, 68), (129, 60), (65, 3), (17, 20), (8, 2), (2, 32)]
    (codeMat 87) (codeMat 273) (codeMat 273) true
    det87 det273 inv273
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0860_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 129, 65, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0860_orbit
  simpa only [lower31] using h

theorem space0861_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [449, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(449, 88), (33, 30), (17, 28), (8, 3), (5, 40), (2, 32)]
    (codeMat 266) (codeMat 425) (codeMat 249) false
    det266 det425 inv425
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0861_lower : 15 ≤ frozenWangTable.L0 (spanCodes [449, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0861_orbit
  simpa only [lower31] using h

theorem space0862_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 135), (64, 45), (34, 134), (19, 404), (10, 166), (4, 2)]
    (codeMat 142) (codeMat 143) (codeMat 482) true
    det142 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0862_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0862_orbit
  simpa only [lower55] using h

theorem space0863_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 135), (64, 45), (35, 132), (19, 306), (10, 166), (4, 2)]
    (codeMat 207) (codeMat 157) (codeMat 486) true
    det207 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0863_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0863_orbit
  simpa only [lower55] using h


end QiushiMatmul.FrozenWang
