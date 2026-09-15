import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0896_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [322, 195, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(322, 168), (195, 45), (34, 436), (19, 306), (10, 404), (6, 2)]
    (codeMat 143) (codeMat 501) (codeMat 494) true
    det143 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0896_lower : 14 ≤ frozenWangTable.L0 (spanCodes [322, 195, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0896_orbit
  simpa only [lower55] using h

theorem space0897_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 128, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 33), (128, 45), (34, 34), (19, 306), (10, 404), (6, 32)]
    (codeMat 93) (codeMat 94) (codeMat 500) true
    det93 det94 inv94
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0897_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0897_orbit
  simpa only [lower55] using h

theorem space0898_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [320, 194, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(320, 3), (194, 287), (34, 406), (19, 166), (10, 404), (6, 32)]
    (codeMat 86) (codeMat 494) (codeMat 501) true
    det86 det494 inv494
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0898_lower : 14 ≤ frozenWangTable.L0 (spanCodes [320, 194, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0898_orbit
  simpa only [lower55] using h

theorem space0899_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [322, 194, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(322, 284), (194, 287), (35, 164), (19, 166), (10, 404), (5, 32)]
    (codeMat 86) (codeMat 458) (codeMat 458) true
    det86 det458 inv458
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0899_lower : 14 ≤ frozenWangTable.L0 (spanCodes [322, 194, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0899_orbit
  simpa only [lower55] using h

theorem space0900_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [323, 195, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(323, 44), (195, 45), (35, 164), (19, 166), (10, 404), (5, 32)]
    (codeMat 84) (codeMat 458) (codeMat 458) true
    det84 det458 inv458
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0900_lower : 14 ≤ frozenWangTable.L0 (spanCodes [323, 195, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0900_orbit
  simpa only [lower55] using h

theorem space0901_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 408), (128, 45), (32, 32), (19, 404), (10, 306), (5, 438)]
    (codeMat 158) (codeMat 115) (codeMat 492) true
    det158 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0901_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0901_orbit
  simpa only [lower55] using h

theorem space0902_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 129, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 14), (129, 441), (32, 32), (19, 404), (10, 306), (5, 438)]
    (codeMat 157) (codeMat 115) (codeMat 492) true
    det157 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0902_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0902_orbit
  simpa only [lower55] using h

theorem space0903_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [321, 194, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(321, 316), (194, 287), (32, 438), (19, 404), (10, 166), (5, 32)]
    (codeMat 94) (codeMat 501) (codeMat 494) true
    det94 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0903_lower : 14 ≤ frozenWangTable.L0 (spanCodes [321, 194, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0903_orbit
  simpa only [lower55] using h

theorem space0904_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 437), (128, 45), (35, 436), (19, 404), (10, 306), (7, 438)]
    (codeMat 158) (codeMat 87) (codeMat 468) true
    det158 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0904_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0904_orbit
  simpa only [lower55] using h

theorem space0905_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 129, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 35), (129, 287), (34, 34), (19, 306), (10, 404), (6, 32)]
    (codeMat 94) (codeMat 94) (codeMat 500) true
    det94 det94 inv94
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0905_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0905_orbit
  simpa only [lower55] using h

theorem space0906_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 129, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (129, 287), (32, 2), (19, 306), (10, 166), (6, 32)]
    (codeMat 86) (codeMat 87) (codeMat 468) true
    det86 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0906_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0906_orbit
  simpa only [lower55] using h

theorem space0907_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [321, 192, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(321, 135), (192, 45), (35, 274), (19, 306), (10, 404), (5, 2)]
    (codeMat 142) (codeMat 465) (codeMat 465) true
    det142 det465 inv465
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0907_lower : 14 ≤ frozenWangTable.L0 (spanCodes [321, 192, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0907_orbit
  simpa only [lower55] using h

theorem space0908_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 129, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 284), (129, 287), (35, 304), (19, 306), (10, 166), (4, 32)]
    (codeMat 86) (codeMat 115) (codeMat 492) true
    det86 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0908_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0908_orbit
  simpa only [lower55] using h

theorem space0909_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [322, 194, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(322, 440), (194, 441), (35, 164), (19, 166), (10, 306), (4, 438)]
    (codeMat 212) (codeMat 501) (codeMat 494) true
    det212 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0909_lower : 14 ≤ frozenWangTable.L0 (spanCodes [322, 194, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0909_orbit
  simpa only [lower55] using h

theorem space0910_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 130, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 33), (130, 32), (64, 2), (19, 306), (10, 166), (4, 45)]
    (codeMat 428) (codeMat 396) (codeMat 106) false
    det428 det396 inv396
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0910_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0910_orbit
  simpa only [lower55] using h

theorem space0911_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (128, 2), (65, 32), (19, 166), (10, 306), (5, 45)]
    (codeMat 492) (codeMat 84) (codeMat 84) false
    det492 det84 inv84
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0911_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0911_orbit
  simpa only [lower55] using h

theorem space0912_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 35), (131, 34), (64, 2), (19, 404), (10, 166), (5, 45)]
    (codeMat 492) (codeMat 444) (codeMat 110) false
    det492 det444 inv444
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0912_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0912_orbit
  simpa only [lower55] using h

theorem space0913_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 128, 67, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 14), (128, 32), (67, 34), (19, 306), (10, 404), (7, 45)]
    (codeMat 421) (codeMat 492) (codeMat 115) false
    det421 det492 inv492
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0913_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0913_orbit
  simpa only [lower55] using h

theorem space0914_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 131, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (131, 34), (64, 2), (19, 404), (10, 166), (6, 45)]
    (codeMat 492) (codeMat 188) (codeMat 103) false
    det492 det188 inv188
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0914_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0914_orbit
  simpa only [lower55] using h

theorem space0915_orbit :
    frozenWangTable.OrbitImage 116 (spanCodes [384, 64, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 116 [(384, 1), (64, 2), (19, 304), (10, 160), (6, 8)]
    (codeMat 140) (codeMat 396) (codeMat 106) false
    det140 det396 inv396
    (by rw [basis116]; decide +kernel)
    (by rw [basis116]; decide +kernel)

theorem space0915_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 64, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 116 space0915_orbit
  simpa only [lower116] using h

theorem space0916_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 130, 64, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 46), (130, 2), (64, 32), (19, 166), (10, 306), (7, 45)]
    (codeMat 421) (codeMat 116) (codeMat 92) false
    det421 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0916_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0916_orbit
  simpa only [lower55] using h

theorem space0917_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 65, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (128, 2), (65, 32), (19, 166), (10, 306), (7, 45)]
    (codeMat 492) (codeMat 116) (codeMat 92) false
    det492 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0917_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0917_orbit
  simpa only [lower55] using h

theorem space0918_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (128, 2), (67, 34), (19, 166), (10, 404), (5, 45)]
    (codeMat 428) (codeMat 124) (codeMat 124) false
    det428 det124 inv124
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0918_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0918_orbit
  simpa only [lower55] using h

theorem space0919_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 130, 64, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 44), (130, 2), (64, 32), (19, 166), (10, 306), (5, 45)]
    (codeMat 421) (codeMat 84) (codeMat 84) false
    det421 det84 inv84
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0919_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0919_orbit
  simpa only [lower55] using h

theorem space0920_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 128, 67, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 46), (128, 32), (67, 34), (19, 306), (10, 404), (5, 45)]
    (codeMat 421) (codeMat 236) (codeMat 123) false
    det421 det236 inv236
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0920_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0920_orbit
  simpa only [lower55] using h

theorem space0921_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 129, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 14), (129, 34), (65, 2), (19, 404), (10, 166), (5, 45)]
    (codeMat 421) (codeMat 444) (codeMat 110) false
    det421 det444 inv444
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0921_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0921_orbit
  simpa only [lower55] using h

theorem space0922_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 65, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 14), (128, 32), (65, 2), (19, 306), (10, 166), (5, 45)]
    (codeMat 485) (codeMat 428) (codeMat 107) false
    det485 det428 inv428
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0922_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0922_orbit
  simpa only [lower55] using h

theorem space0923_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 130, 64, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 12), (130, 2), (64, 32), (19, 166), (10, 306), (4, 45)]
    (codeMat 421) (codeMat 340) (codeMat 85) false
    det421 det340 inv340
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0923_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0923_orbit
  simpa only [lower55] using h

theorem space0924_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 64, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 437), (131, 436), (64, 2), (32, 45), (19, 404), (10, 306)]
    (codeMat 500) (codeMat 396) (codeMat 106) false
    det500 det396 inv396
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0924_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0924_orbit
  simpa only [lower55] using h

theorem space0925_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 128, 65, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 437), (128, 2), (65, 438), (32, 45), (19, 306), (10, 166)]
    (codeMat 500) (codeMat 348) (codeMat 125) false
    det500 det348 inv348
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0925_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0925_orbit
  simpa only [lower55] using h

theorem space0926_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 128, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 135), (128, 2), (66, 134), (32, 45), (19, 404), (10, 166)]
    (codeMat 372) (codeMat 340) (codeMat 85) false
    det372 det340 inv340
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0926_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0926_orbit
  simpa only [lower55] using h

theorem space0927_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 129, 64, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (129, 132), (64, 2), (33, 139), (19, 306), (10, 404)]
    (codeMat 372) (codeMat 156) (codeMat 102) false
    det372 det156 inv156
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0927_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0927_orbit
  simpa only [lower55] using h


end QiushiMatmul.FrozenWang
