import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1856_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [288, 128, 98, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(288, 27), (128, 260), (98, 94), (17, 160), (10, 176), (5, 320)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    det93 det236 inv236
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1856_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 98, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space1856_orbit
  simpa only [lower65] using h

theorem space1857_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [289, 160, 66, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(289, 69), (160, 186), (66, 420), (16, 16), (10, 160), (4, 320)]
    (codeMat 87) (codeMat 340) (codeMat 85) false
    det87 det340 inv340
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1857_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 160, 66, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1857_orbit
  simpa only [lower65] using h

theorem space1858_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 160, 96, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 69), (160, 170), (96, 430), (16, 16), (10, 176), (4, 320)]
    (codeMat 85) (codeMat 348) (codeMat 125) false
    det85 det348 inv348
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1858_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 160, 96, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1858_orbit
  simpa only [lower65] using h

theorem space1859_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 160, 100, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 1), (160, 79), (100, 69), (20, 496), (9, 320), (3, 16)]
    (codeMat 204) (codeMat 215) (codeMat 342) false
    det204 det215 inv215
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1859_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 100, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space1859_orbit
  simpa only [lower65] using h

theorem space1860_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [288, 133, 96, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(288, 260), (133, 10), (96, 261), (20, 160), (8, 320), (2, 16)]
    (codeMat 140) (codeMat 337) (codeMat 337) false
    det140 det337 inv337
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1860_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 133, 96, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space1860_orbit
  simpa only [lower65] using h

theorem space1861_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [292, 164, 70, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(292, 260), (164, 276), (70, 10), (20, 436), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 401) (codeMat 401) false
    det417 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1861_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 164, 70, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1861_orbit
  simpa only [lower65] using h

theorem space1862_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [288, 160, 70, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(288, 16), (160, 336), (70, 69), (20, 506), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 179) (codeMat 421) false
    det305 det179 inv179
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1862_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 160, 70, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1862_orbit
  simpa only [lower65] using h

theorem space1863_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 128, 64, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 139), (128, 9), (64, 1), (20, 252), (10, 31), (1, 3)]
    (codeMat 172) (codeMat 307) (codeMat 311) true
    det172 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1863_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 64, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1863_orbit
  simpa only [lower35] using h

theorem space1864_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 135, 65, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 496), (135, 160), (65, 320), (32, 1), (20, 78), (10, 437)]
    (codeMat 354) (codeMat 213) (codeMat 470) false
    det354 det213 inv213
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1864_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 135, 65, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1864_orbit
  simpa only [lower65] using h

theorem space1865_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [262, 133, 67, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(262, 496), (133, 336), (67, 480), (32, 1), (20, 79), (10, 507)]
    (codeMat 298) (codeMat 159) (codeMat 230) false
    det298 det159 inv159
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1865_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 133, 67, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1865_orbit
  simpa only [lower65] using h

theorem space1866_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 68, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (132, 22), (68, 148), (32, 3), (20, 31), (10, 252)]
    (codeMat 102) (codeMat 94) (codeMat 500) true
    det102 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1866_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1866_orbit
  simpa only [lower35] using h

theorem space1867_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 68, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (135, 149), (68, 150), (34, 104), (20, 96), (10, 232)]
    (codeMat 157) (codeMat 458) (codeMat 458) false
    det157 det458 inv458
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1867_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1867_orbit
  simpa only [lower35] using h

theorem space1868_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 132, 64, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 176), (132, 480), (64, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 299) (codeMat 339) (codeMat 467) false
    det299 det339 inv339
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1868_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 132, 64, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1868_orbit
  simpa only [lower65] using h

theorem space1869_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 130, 68, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 148), (130, 128), (68, 150), (39, 252), (20, 224), (10, 255)]
    (codeMat 110) (codeMat 489) (codeMat 241) true
    det110 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1869_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 68, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1869_orbit
  simpa only [lower35] using h

theorem space1870_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 196, 33, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 32), (196, 34), (33, 440), (20, 463), (10, 118)]
    (codeMat 355) (codeMat 242) (codeMat 205) true
    det355 det242 inv242
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1870_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 196, 33, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1870_orbit
  simpa only [lower144] using h

theorem space1871_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [385, 65, 33, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(385, 34), (65, 32), (33, 463), (20, 118), (10, 440)]
    (codeMat 355) (codeMat 428) (codeMat 107) true
    det355 det428 inv428
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1871_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 65, 33, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1871_orbit
  simpa only [lower144] using h

theorem space1872_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 131, 64, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 496), (131, 336), (64, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 354) (codeMat 158) (codeMat 358) false
    det354 det158 inv158
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1872_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1872_orbit
  simpa only [lower65] using h

theorem space1873_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 129, 66, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 496), (129, 160), (66, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 298) (codeMat 212) (codeMat 86) false
    det298 det212 inv212
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1873_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1873_orbit
  simpa only [lower65] using h

theorem space1874_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 71, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 1), (130, 9), (71, 104), (32, 3), (20, 31), (10, 252)]
    (codeMat 125) (codeMat 94) (codeMat 500) true
    det125 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1874_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 71, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1874_orbit
  simpa only [lower35] using h

theorem space1875_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 129, 64, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 436), (129, 78), (64, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 156) (codeMat 401) (codeMat 401) false
    det156 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1875_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1875_orbit
  simpa only [lower65] using h

theorem space1876_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 130, 64, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 238), (130, 260), (64, 27), (34, 160), (20, 176), (10, 480)]
    (codeMat 159) (codeMat 425) (codeMat 249) false
    det159 det425 inv425
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1876_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1876_orbit
  simpa only [lower65] using h

theorem space1877_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [261, 129, 65, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(261, 245), (129, 287), (65, 27), (36, 320), (20, 336), (10, 480)]
    (codeMat 215) (codeMat 415) (codeMat 253) false
    det215 det415 inv415
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1877_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1877_orbit
  simpa only [lower65] using h

theorem space1878_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [263, 131, 65, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(263, 437), (131, 79), (65, 1), (36, 320), (20, 336), (10, 496)]
    (codeMat 213) (codeMat 407) (codeMat 405) false
    det213 det407 inv407
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1878_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 131, 65, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1878_orbit
  simpa only [lower65] using h

theorem space1879_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 128, 66, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 320), (128, 16), (66, 176), (39, 437), (20, 506), (10, 436)]
    (codeMat 355) (codeMat 340) (codeMat 85) false
    det355 det340 inv340
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1879_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 66, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1879_orbit
  simpa only [lower65] using h

theorem space1880_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 70, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 104), (134, 96), (70, 105), (39, 252), (20, 224), (10, 255)]
    (codeMat 124) (codeMat 489) (codeMat 241) true
    det124 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1880_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 70, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space1880_orbit
  simpa only [lower35] using h

theorem space1881_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [324, 131, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(324, 495), (131, 493), (38, 441), (20, 462), (10, 118)]
    (codeMat 426) (codeMat 351) (codeMat 239) true
    det426 det351 inv351
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1881_lower : 15 ≤ frozenWangTable.L0 (spanCodes [324, 131, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1881_orbit
  simpa only [lower144] using h

theorem space1882_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [320, 135, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(320, 32), (135, 34), (38, 462), (20, 441), (10, 118)]
    (codeMat 298) (codeMat 370) (codeMat 207) true
    det298 det370 inv370
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1882_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 135, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1882_orbit
  simpa only [lower144] using h

theorem space1883_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [391, 64, 38, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(391, 34), (64, 32), (38, 119), (20, 462), (10, 440)]
    (codeMat 298) (codeMat 412) (codeMat 111) true
    det298 det412 inv412
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1883_lower : 15 ≤ frozenWangTable.L0 (spanCodes [391, 64, 38, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space1883_orbit
  simpa only [lower144] using h

theorem space1884_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [294, 132, 66, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(294, 139), (132, 245), (66, 30), (20, 252), (10, 31), (1, 3)]
    (codeMat 190) (codeMat 307) (codeMat 311) true
    det190 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1884_lower : 15 ≤ frozenWangTable.L0 (spanCodes [294, 132, 66, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1884_orbit
  simpa only [lower35] using h

theorem space1885_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 160, 68, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 260), (160, 160), (68, 68), (20, 436), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    det305 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1885_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 160, 68, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1885_orbit
  simpa only [lower65] using h

theorem space1886_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [256, 164, 68, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(256, 16), (164, 170), (68, 10), (20, 506), (10, 79), (1, 1)]
    (codeMat 417) (codeMat 179) (codeMat 421) false
    det417 det179 inv179
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1886_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 164, 68, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1886_orbit
  simpa only [lower65] using h

theorem space1887_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 135, 67, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 260), (135, 238), (67, 497), (34, 176), (20, 160), (10, 496)]
    (codeMat 159) (codeMat 401) (codeMat 401) false
    det159 det401 inv401
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1887_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 135, 67, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space1887_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
