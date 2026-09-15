import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1824_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [325, 197, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(325, 40), (197, 43), (34, 134), (20, 132), (10, 166)]
    (codeMat 159) (codeMat 458) (codeMat 458) true
    det159 det458 inv458
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1824_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 197, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1824_orbit
  simpa only [lower103] using h

theorem space1825_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [260, 130, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(260, 8), (130, 9), (36, 32), (20, 34), (10, 166)]
    (codeMat 213) (codeMat 122) (codeMat 460) true
    det213 det122 inv122
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1825_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1825_orbit
  simpa only [lower103] using h

theorem space1826_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 134, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 40), (134, 43), (36, 32), (20, 34), (10, 166)]
    (codeMat 215) (codeMat 122) (codeMat 460) true
    det215 det122 inv122
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1826_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 134, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1826_orbit
  simpa only [lower103] using h

theorem space1827_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [260, 132, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(260, 40), (132, 43), (36, 32), (20, 34), (10, 166)]
    (codeMat 214) (codeMat 122) (codeMat 460) true
    det214 det122 inv122
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1827_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1827_orbit
  simpa only [lower103] using h

theorem space1828_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 128, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 8), (128, 9), (36, 32), (20, 34), (10, 166)]
    (codeMat 212) (codeMat 122) (codeMat 460) true
    det212 det122 inv122
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1828_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1828_orbit
  simpa only [lower103] using h

theorem space1829_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [320, 198, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(320, 40), (198, 43), (34, 134), (20, 132), (10, 166)]
    (codeMat 158) (codeMat 458) (codeMat 458) true
    det158 det458 inv458
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1829_lower : 15 ≤ frozenWangTable.L0 (spanCodes [320, 198, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1829_orbit
  simpa only [lower103] using h

theorem space1830_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [325, 195, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(325, 8), (195, 9), (34, 134), (20, 132), (10, 166)]
    (codeMat 157) (codeMat 458) (codeMat 458) true
    det157 det458 inv458
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1830_lower : 15 ≤ frozenWangTable.L0 (spanCodes [325, 195, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 103 space1830_orbit
  simpa only [lower103] using h

theorem space1831_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [288, 128, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(288, 8), (128, 3), (16, 2), (10, 132), (4, 32)]
    (codeMat 86) (codeMat 98) (codeMat 140) true
    det86 det98 inv98
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1831_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 128, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space1831_orbit
  simpa only [lower103] using h

theorem space1832_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 130, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 52), (130, 54), (32, 8), (16, 9), (10, 100), (4, 32)]
    (codeMat 98) (codeMat 114) (codeMat 204) true
    det98 det114 inv114
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1832_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 31 space1832_orbit
  simpa only [lower31] using h

theorem space1833_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [354, 195, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(354, 140), (195, 3), (17, 134), (10, 132), (5, 32)]
    (codeMat 94) (codeMat 482) (codeMat 143) true
    det94 det482 inv482
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1833_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 195, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space1833_orbit
  simpa only [lower103] using h

theorem space1834_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [323, 192, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(323, 20), (192, 2), (34, 100), (17, 77), (10, 76), (5, 32)]
    (codeMat 99) (codeMat 474) (codeMat 395) true
    det99 det474 inv474
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1834_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 192, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 31 space1834_orbit
  simpa only [lower31] using h

theorem space1835_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [288, 130, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(288, 40), (130, 3), (16, 2), (10, 132), (4, 32)]
    (codeMat 87) (codeMat 98) (codeMat 140) true
    det87 det98 inv98
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1835_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 130, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space1835_orbit
  simpa only [lower103] using h

theorem space1836_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 20), (128, 2), (32, 8), (16, 1), (10, 68), (4, 32)]
    (codeMat 98) (codeMat 98) (codeMat 140) true
    det98 det98 inv98
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1836_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 31 space1836_orbit
  simpa only [lower31] using h

theorem space1837_orbit :
    frozenWangTable.OrbitImage 158 (spanCodes [326, 192, 33, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 158 [(326, 33), (192, 32), (33, 245), (20, 222), (10, 235)]
    (codeMat 309) (codeMat 499) (codeMat 382) true
    det309 det499 inv499
    (by rw [basis158]; decide +kernel)
    (by rw [basis158]; decide +kernel)

theorem space1837_lower : 15 ≤ frozenWangTable.L0 (spanCodes [326, 192, 33, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 158 space1837_orbit
  simpa only [lower158] using h

theorem space1838_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [354, 192, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(354, 172), (192, 3), (17, 134), (10, 132), (5, 32)]
    (codeMat 95) (codeMat 482) (codeMat 143) true
    det95 det482 inv482
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space1838_lower : 15 ≤ frozenWangTable.L0 (spanCodes [354, 192, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space1838_orbit
  simpa only [lower103] using h

theorem space1839_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [323, 195, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(323, 52), (195, 54), (34, 68), (17, 101), (10, 108), (5, 32)]
    (codeMat 99) (codeMat 458) (codeMat 458) true
    det99 det458 inv458
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space1839_lower : 15 ≤ frozenWangTable.L0 (spanCodes [323, 195, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 31 space1839_orbit
  simpa only [lower31] using h

theorem space1840_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 130, 64, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 139), (130, 9), (64, 2), (20, 252), (10, 31), (1, 3)]
    (codeMat 165) (codeMat 307) (codeMat 311) true
    det165 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1840_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1840_orbit
  simpa only [lower35] using h

theorem space1841_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [292, 162, 70, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(292, 27), (162, 287), (70, 68), (20, 507), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 183) (codeMat 419) false
    det305 det183 inv183
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1841_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 162, 70, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space1841_orbit
  simpa only [lower65] using h

theorem space1842_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [292, 133, 97, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(292, 260), (133, 26), (97, 261), (20, 160), (8, 320), (2, 16)]
    (codeMat 141) (codeMat 337) (codeMat 337) false
    det141 det337 inv337
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1842_lower : 15 ≤ frozenWangTable.L0 (spanCodes [292, 133, 97, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 65 space1842_orbit
  simpa only [lower65] using h

theorem space1843_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 64, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 22), (128, 3), (64, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 204) (codeMat 314) (codeMat 271) false
    det204 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1843_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space1843_orbit
  simpa only [lower35] using h

theorem space1844_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 161, 101, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 1), (161, 95), (101, 69), (20, 496), (9, 320), (3, 16)]
    (codeMat 205) (codeMat 215) (codeMat 342) false
    det205 det215 inv215
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1844_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 161, 101, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 65 space1844_orbit
  simpa only [lower65] using h

theorem space1845_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 64, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 20), (128, 1), (64, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 266) (codeMat 266) false
    det140 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1845_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space1845_orbit
  simpa only [lower35] using h

theorem space1846_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 130, 64, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 128), (130, 8), (64, 2), (20, 224), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 273) (codeMat 273) true
    det165 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1846_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1846_orbit
  simpa only [lower35] using h

theorem space1847_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [289, 162, 67, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(289, 261), (162, 186), (67, 420), (16, 16), (10, 160), (4, 320)]
    (codeMat 86) (codeMat 340) (codeMat 85) false
    det86 det340 inv340
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1847_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 162, 67, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 65 space1847_orbit
  simpa only [lower65] using h

theorem space1848_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 163, 96, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 246), (163, 157), (96, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    det94 det482 inv482
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1848_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 163, 96, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space1848_orbit
  simpa only [lower35] using h

theorem space1849_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [289, 163, 66, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(289, 321), (163, 254), (66, 420), (17, 176), (10, 160), (5, 320)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    det95 det212 inv212
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1849_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 163, 66, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space1849_orbit
  simpa only [lower65] using h

theorem space1850_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [289, 130, 99, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(289, 347), (130, 260), (99, 94), (17, 160), (10, 176), (5, 320)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    det92 det236 inv236
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space1850_lower : 15 ≤ frozenWangTable.L0 (spanCodes [289, 130, 99, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 65 space1850_orbit
  simpa only [lower65] using h

theorem space1851_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 128, 64, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (128, 8), (64, 1), (20, 224), (10, 28), (1, 3)]
    (codeMat 172) (codeMat 273) (codeMat 273) true
    det172 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1851_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 64, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space1851_orbit
  simpa only [lower35] using h

theorem space1852_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 65, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 20), (128, 9), (65, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 141) (codeMat 266) (codeMat 266) false
    det141 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1852_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space1852_orbit
  simpa only [lower35] using h

theorem space1853_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 129, 65, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 22), (129, 11), (65, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 205) (codeMat 314) (codeMat 271) false
    det205 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space1853_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 129, 65, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space1853_orbit
  simpa only [lower35] using h

theorem space1854_orbit :
    frozenWangTable.OrbitImage 192 (spanCodes [258, 135, 66, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 192 [(258, 43), (135, 33), (66, 42), (20, 350), (10, 469)]
    (codeMat 492) (codeMat 491) (codeMat 375) false
    det492 det491 inv491
    (by rw [basis192]; decide +kernel)
    (by rw [basis192]; decide +kernel)

theorem space1854_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 66, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 192 space1854_orbit
  simpa only [lower192] using h

theorem space1855_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [291, 227, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(291, 33), (227, 35), (19, 462), (10, 441), (7, 1)]
    (codeMat 481) (codeMat 234) (codeMat 461) true
    det481 det234 inv234
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space1855_lower : 15 ≤ frozenWangTable.L0 (spanCodes [291, 227, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 144 space1855_orbit
  simpa only [lower144] using h


end QiushiMatmul.FrozenWang
