import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1888_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 66, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (128, 8), (66, 96), (32, 3), (20, 28), (10, 224)]
    (codeMat 116) (codeMat 84) (codeMat 84) true
    det116 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1888_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1888_orbit
  simpa only [lower35] using h

theorem space1889_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 133, 64, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 128), (133, 150), (64, 130), (39, 224), (20, 255), (10, 227)]
    (codeMat 103) (codeMat 467) (codeMat 339) true
    det103 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1889_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 64, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1889_orbit
  simpa only [lower35] using h

theorem space1890_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 132, 70, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 130), (132, 139), (70, 126), (36, 128), (20, 136), (10, 232)]
    (codeMat 214) (codeMat 122) (codeMat 460) false
    det214 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1890_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 70, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1890_orbit
  simpa only [lower35] using h

theorem space1891_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [293, 132, 65, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(293, 20), (132, 105), (65, 130), (20, 96), (8, 128), (2, 8)]
    (codeMat 143) (codeMat 266) (codeMat 266) false
    det143 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1891_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 132, 65, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space1891_orbit
  simpa only [lower35] using h

theorem space1892_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [288, 164, 101, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(288, 1), (164, 447), (101, 261), (20, 496), (9, 320), (3, 16)]
    (codeMat 206) (codeMat 215) (codeMat 342) false
    det206 det215 inv215
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1892_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 164, 101, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space1892_orbit
  simpa only [lower65] using h

theorem space1893_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 129, 71, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 252), (129, 245), (71, 126), (34, 104), (20, 96), (10, 232)]
    (codeMat 158) (codeMat 458) (codeMat 458) false
    det158 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1893_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 71, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1893_orbit
  simpa only [lower35] using h

theorem space1894_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 134, 65, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 2), (134, 20), (65, 128), (32, 3), (20, 28), (10, 224)]
    (codeMat 111) (codeMat 84) (codeMat 84) true
    det111 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1894_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 134, 65, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1894_orbit
  simpa only [lower35] using h

theorem space1895_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 129, 66, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 96), (129, 105), (66, 97), (39, 224), (20, 255), (10, 227)]
    (codeMat 117) (codeMat 467) (codeMat 339) true
    det117 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1895_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 129, 66, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1895_orbit
  simpa only [lower35] using h

theorem space1896_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 135, 67, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 245), (135, 287), (67, 497), (36, 320), (20, 336), (10, 496)]
    (codeMat 215) (codeMat 407) (codeMat 405) false
    det215 det407 inv407
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1896_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 67, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1896_orbit
  simpa only [lower65] using h

theorem space1897_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [293, 133, 64, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(293, 22), (133, 227), (64, 130), (20, 232), (9, 128), (3, 8)]
    (codeMat 207) (codeMat 314) (codeMat 271) false
    det207 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1897_lower : 15 ≤ frozenWangTable.L0 (spanCodes [293, 133, 64, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space1897_orbit
  simpa only [lower35] using h

theorem space1898_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 129, 96, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 260), (129, 170), (96, 69), (20, 160), (8, 320), (2, 16)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    det142 det337 inv337
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1898_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 96, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space1898_orbit
  simpa only [lower65] using h

theorem space1899_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [292, 132, 66, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(292, 128), (132, 232), (66, 29), (20, 224), (10, 28), (1, 3)]
    (codeMat 190) (codeMat 273) (codeMat 273) true
    det190 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1899_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 132, 66, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1899_orbit
  simpa only [lower35] using h

theorem space1900_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 133, 66, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 245), (133, 287), (66, 497), (36, 320), (20, 336), (10, 496)]
    (codeMat 214) (codeMat 407) (codeMat 405) false
    det214 det407 inv407
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1900_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 133, 66, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1900_orbit
  simpa only [lower65] using h

theorem space1901_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 67, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 96), (131, 105), (67, 97), (39, 224), (20, 255), (10, 227)]
    (codeMat 124) (codeMat 467) (codeMat 339) true
    det124 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1901_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1901_orbit
  simpa only [lower35] using h

theorem space1902_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 64, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (132, 20), (64, 128), (32, 3), (20, 28), (10, 224)]
    (codeMat 102) (codeMat 84) (codeMat 84) true
    det102 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1902_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1902_orbit
  simpa only [lower35] using h

theorem space1903_orbit :
    frozenWangTable.OrbitImage 69 (spanCodes [256, 135, 66, 33, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 69 [(256, 27), (135, 175), (66, 353), (33, 479), (20, 430), (10, 97)]
    (codeMat 415) (codeMat 230) (codeMat 159) false
    det415 det230 inv230
    (by rw [basis69]; decide +kernel)
    (by rw [basis69]; decide +kernel)

theorem space1903_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 135, 66, 33, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 69 space1903_orbit
  simpa only [lower69] using h

theorem space1904_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 70, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 252), (131, 245), (70, 126), (34, 104), (20, 96), (10, 232)]
    (codeMat 159) (codeMat 458) (codeMat 458) false
    det159 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1904_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 70, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1904_orbit
  simpa only [lower35] using h

theorem space1905_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 96, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 1), (96, 20), (16, 8), (10, 96), (4, 128)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    det84 det98 inv98
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1905_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 96, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space1905_orbit
  simpa only [lower35] using h

theorem space1906_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 160, 65, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 1), (160, 78), (65, 260), (17, 176), (10, 160), (5, 320)]
    (codeMat 92) (codeMat 212) (codeMat 86) false
    det92 det212 inv212
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1906_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 65, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space1906_orbit
  simpa only [lower65] using h

theorem space1907_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 134, 71, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 130), (134, 139), (71, 126), (36, 128), (20, 136), (10, 232)]
    (codeMat 215) (codeMat 122) (codeMat 460) false
    det215 det122 inv122
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1907_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 71, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1907_orbit
  simpa only [lower35] using h

theorem space1908_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 135, 65, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (135, 150), (65, 130), (39, 224), (20, 255), (10, 227)]
    (codeMat 110) (codeMat 467) (codeMat 339) true
    det110 det467 inv467
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1908_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 65, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1908_orbit
  simpa only [lower35] using h

theorem space1909_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 67, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 1), (130, 8), (67, 96), (32, 3), (20, 28), (10, 224)]
    (codeMat 125) (codeMat 84) (codeMat 84) true
    det125 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1909_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 67, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1909_orbit
  simpa only [lower35] using h

theorem space1910_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 133, 66, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 260), (133, 238), (66, 497), (34, 176), (20, 160), (10, 496)]
    (codeMat 158) (codeMat 401) (codeMat 401) false
    det158 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1910_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 133, 66, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1910_orbit
  simpa only [lower65] using h

theorem space1911_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 160, 64, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 69), (160, 170), (64, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    det85 det340 inv340
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1911_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 160, 64, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1911_orbit
  simpa only [lower65] using h

theorem space1912_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [288, 134, 66, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(288, 128), (134, 232), (66, 30), (20, 224), (10, 28), (1, 3)]
    (codeMat 183) (codeMat 273) (codeMat 273) true
    det183 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1912_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 134, 66, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1912_orbit
  simpa only [lower35] using h

theorem space1913_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [261, 197, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(261, 493), (197, 495), (38, 462), (20, 119), (10, 440)]
    (codeMat 482) (codeMat 244) (codeMat 95) true
    det482 det244 inv244
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1913_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 197, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1913_orbit
  simpa only [lower144] using h

theorem space1914_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [259, 195, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(259, 34), (195, 32), (38, 441), (20, 119), (10, 463)]
    (codeMat 354) (codeMat 239) (codeMat 351) true
    det354 det239 inv239
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1914_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 195, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1914_orbit
  simpa only [lower144] using h

theorem space1915_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [387, 67, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(387, 493), (67, 495), (38, 119), (20, 441), (10, 463)]
    (codeMat 482) (codeMat 426) (codeMat 335) true
    det482 det426 inv426
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1915_lower : 15 ≤ frozenWangTable.L0 (spanCodes [387, 67, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1915_orbit
  simpa only [lower144] using h

theorem space1916_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 71, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 104), (132, 96), (71, 105), (39, 252), (20, 224), (10, 255)]
    (codeMat 117) (codeMat 489) (codeMat 241) true
    det117 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1916_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1916_orbit
  simpa only [lower35] using h

theorem space1917_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 129, 64, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 437), (129, 79), (64, 1), (36, 320), (20, 336), (10, 496)]
    (codeMat 212) (codeMat 407) (codeMat 405) false
    det212 det407 inv407
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1917_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1917_orbit
  simpa only [lower65] using h

theorem space1918_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 131, 65, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 436), (131, 78), (65, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 157) (codeMat 401) (codeMat 401) false
    det157 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1918_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 131, 65, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1918_orbit
  simpa only [lower65] using h

theorem space1919_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 70, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (128, 9), (70, 104), (32, 3), (20, 31), (10, 252)]
    (codeMat 116) (codeMat 94) (codeMat 500) true
    det116 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1919_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 70, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1919_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
