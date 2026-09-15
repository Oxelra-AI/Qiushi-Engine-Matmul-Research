import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0320_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 65, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 3), (132, 35), (65, 1), (19, 462), (10, 119)]
    (codeMat 421) (codeMat 183) (codeMat 419) false
    det421 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0320_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 65, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0320_orbit
  simpa only [lower144] using h

theorem space0321_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 163, 98, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (163, 84), (98, 492), (19, 119), (10, 462)]
    (codeMat 358) (codeMat 474) (codeMat 395) false
    det358 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0321_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 163, 98, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0321_orbit
  simpa only [lower144] using h

theorem space0322_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 129, 100, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (129, 440), (100, 34), (19, 441), (10, 462)]
    (codeMat 359) (codeMat 106) (codeMat 396) false
    det359 det106 inv106
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0322_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 129, 100, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0322_orbit
  simpa only [lower144] using h

theorem space0323_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 160, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (160, 34), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 177) (codeMat 417) false
    det358 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0323_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0323_orbit
  simpa only [lower144] using h

theorem space0324_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 165, 103, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (165, 492), (103, 84), (19, 462), (10, 119)]
    (codeMat 359) (codeMat 473) (codeMat 409) false
    det359 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0324_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 165, 103, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0324_orbit
  simpa only [lower144] using h

theorem space0325_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [257, 128, 64, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(257, 100), (128, 1), (64, 9), (16, 2), (9, 54), (3, 32)]
    (codeMat 84) (codeMat 267) (codeMat 282) true
    det84 det267 inv267
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0325_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 31 space0325_orbit
  simpa only [lower31] using h

theorem space0326_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 164, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (164, 35), (67, 440), (19, 119), (10, 441)]
    (codeMat 359) (codeMat 183) (codeMat 419) false
    det359 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0326_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0326_orbit
  simpa only [lower144] using h

theorem space0327_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 134, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 32), (134, 34), (69, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 473) (codeMat 409) false
    det421 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0327_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0327_orbit
  simpa only [lower144] using h

theorem space0328_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 131, 96, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (131, 440), (96, 35), (19, 441), (10, 119)]
    (codeMat 358) (codeMat 111) (codeMat 412) false
    det358 det111 inv111
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0328_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 131, 96, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0328_orbit
  simpa only [lower144] using h

theorem space0329_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [257, 128, 64, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(257, 68), (128, 8), (64, 1), (17, 20), (8, 2), (2, 32)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    det84 det273 inv273
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0329_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 31 space0329_orbit
  simpa only [lower31] using h

theorem space0330_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 64, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 100), (128, 9), (64, 8), (18, 54), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 282) (codeMat 267) true
    det84 det282 inv282
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space0330_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space0330_orbit
  simpa only [lower31] using h

theorem space0331_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 68, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (132, 35), (68, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 474) (codeMat 395) false
    det428 det474 inv474
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0331_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0331_orbit
  simpa only [lower144] using h

theorem space0332_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 166, 66, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 3), (166, 35), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 183) (codeMat 419) false
    det302 det183 inv183
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0332_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 166, 66, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0332_orbit
  simpa only [lower144] using h

theorem space0333_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 129, 97, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 3), (129, 440), (97, 35), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 111) (codeMat 412) false
    det303 det111 inv111
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0333_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 129, 97, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0333_orbit
  simpa only [lower144] using h

theorem space0334_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [288, 224, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(288, 2), (224, 34), (19, 441), (10, 462), (4, 1)]
    (codeMat 305) (codeMat 213) (codeMat 470) true
    det305 det213 inv213
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0334_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 224, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space0334_orbit
  simpa only [lower144] using h

theorem space0335_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [321, 129, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(321, 37), (129, 53), (19, 245), (10, 350), (4, 36)]
    (codeMat 485) (codeMat 339) (codeMat 467) false
    det485 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0335_lower : 15 ≤ frozenWangTable.L0 (spanCodes [321, 129, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0335_orbit
  simpa only [lower220] using h

theorem space0336_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [386, 66, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(386, 37), (66, 53), (19, 350), (10, 245), (4, 36)]
    (codeMat 421) (codeMat 395) (codeMat 474) false
    det421 det395 inv395
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space0336_lower : 15 ≤ frozenWangTable.L0 (spanCodes [386, 66, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space0336_orbit
  simpa only [lower220] using h

theorem space0337_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 162, 67, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 26), (162, 362), (67, 112), (19, 463), (10, 113), (4, 16)]
    (codeMat 271) (codeMat 179) (codeMat 421) false
    det271 det179 inv179
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0337_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 162, 67, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0337_orbit
  simpa only [lower69] using h

theorem space0338_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 163, 96, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 26), (163, 181), (96, 180), (19, 463), (10, 446), (4, 16)]
    (codeMat 461) (codeMat 250) (codeMat 397) false
    det461 det250 inv250
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0338_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 163, 96, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0338_orbit
  simpa only [lower69] using h

theorem space0339_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [290, 131, 97, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(290, 10), (131, 112), (97, 378), (19, 113), (10, 463), (4, 16)]
    (codeMat 270) (codeMat 107) (codeMat 428) false
    det270 det107 inv107
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0339_lower : 15 ≤ frozenWangTable.L0 (spanCodes [290, 131, 97, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0339_orbit
  simpa only [lower69] using h

theorem space0340_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 160, 99, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 26), (160, 164), (99, 165), (19, 446), (10, 463), (4, 16)]
    (codeMat 397) (codeMat 249) (codeMat 425) false
    det397 det249 inv249
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0340_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 160, 99, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 69 space0340_orbit
  simpa only [lower69] using h

theorem space0341_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [289, 162, 66, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(289, 11), (162, 283), (66, 112), (19, 463), (10, 113), (5, 16)]
    (codeMat 334) (codeMat 183) (codeMat 419) false
    det334 det183 inv183
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0341_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 162, 66, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0341_orbit
  simpa only [lower69] using h

theorem space0342_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 160, 97, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (160, 196), (97, 180), (19, 463), (10, 446), (5, 16)]
    (codeMat 270) (codeMat 474) (codeMat 395) false
    det270 det474 inv474
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0342_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 97, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 69 space0342_orbit
  simpa only [lower69] using h

theorem space0343_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 160, 98, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 256), (160, 164), (98, 212), (19, 446), (10, 463), (6, 16)]
    (codeMat 271) (codeMat 473) (codeMat 409) false
    det271 det473 inv473
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0343_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 98, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0343_orbit
  simpa only [lower69] using h

theorem space0344_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [288, 129, 99, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(288, 27), (129, 112), (99, 267), (19, 113), (10, 463), (6, 16)]
    (codeMat 335) (codeMat 111) (codeMat 412) false
    det335 det111 inv111
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0344_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 129, 99, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 69 space0344_orbit
  simpa only [lower69] using h

theorem space0345_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 160, 96, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 11), (160, 196), (96, 197), (19, 463), (10, 446), (7, 16)]
    (codeMat 396) (codeMat 254) (codeMat 443) false
    det396 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0345_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 160, 96, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0345_orbit
  simpa only [lower69] using h

theorem space0346_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 162, 97, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (162, 196), (97, 197), (19, 463), (10, 446), (7, 16)]
    (codeMat 461) (codeMat 254) (codeMat 443) false
    det461 det254 inv254
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0346_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 162, 97, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0346_orbit
  simpa only [lower69] using h

theorem space0347_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 161, 98, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (161, 213), (98, 212), (19, 446), (10, 463), (7, 16)]
    (codeMat 397) (codeMat 253) (codeMat 415) false
    det397 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0347_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 161, 98, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0347_orbit
  simpa only [lower69] using h

theorem space0348_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [259, 163, 99, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(259, 11), (163, 213), (99, 212), (19, 446), (10, 463), (7, 16)]
    (codeMat 460) (codeMat 253) (codeMat 415) false
    det460 det253 inv253
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space0348_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 163, 99, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 69 space0348_orbit
  simpa only [lower69] using h

theorem space0349_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [256, 128, 69, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(256, 3), (128, 1), (69, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 111) (codeMat 412) false
    det428 det111 inv111
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0349_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 69, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0349_orbit
  simpa only [lower144] using h

theorem space0350_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [292, 162, 67, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(292, 2), (162, 34), (67, 440), (19, 462), (10, 441)]
    (codeMat 303) (codeMat 177) (codeMat 417) false
    det303 det177 inv177
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0350_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 67, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0350_orbit
  simpa only [lower144] using h

theorem space0351_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 167, 102, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (167, 492), (102, 84), (19, 462), (10, 119)]
    (codeMat 302) (codeMat 473) (codeMat 409) false
    det302 det473 inv473
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space0351_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 167, 102, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space0351_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
