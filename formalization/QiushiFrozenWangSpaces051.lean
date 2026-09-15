import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1632_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (128, 2), (65, 325), (32, 8), (17, 336), (8, 40), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 85) (codeMat 340) false
    det84 det85 inv85
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1632_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1632_orbit
  simpa only [lower3] using h

theorem space1633_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 196), (128, 1), (64, 3), (32, 32), (16, 8), (9, 216), (4, 256), (3, 128)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    det84 det267 inv267
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1633_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1633_orbit
  simpa only [lower3] using h

theorem space1634_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 452), (129, 453), (65, 455), (32, 32), (16, 40), (9, 504), (4, 256), (3, 128)]
    (codeMat 84) (codeMat 459) (codeMat 346) false
    det84 det459 inv459
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1634_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1634_orbit
  simpa only [lower3] using h

theorem space1635_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 453), (128, 1), (65, 455), (32, 40), (16, 8), (9, 504), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 335) (codeMat 426) false
    det84 det335 inv335
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1635_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1635_orbit
  simpa only [lower3] using h

theorem space1636_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (129, 453), (65, 455), (32, 8), (16, 40), (9, 504), (5, 384), (3, 128)]
    (codeMat 84) (codeMat 207) (codeMat 370) false
    det84 det207 inv207
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1636_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1636_orbit
  simpa only [lower3] using h

theorem space1637_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 199), (128, 1), (64, 3), (33, 248), (16, 8), (9, 216), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 303) (codeMat 286) false
    det84 det303 inv303
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1637_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1637_orbit
  simpa only [lower3] using h

theorem space1638_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (128, 1), (65, 455), (33, 472), (16, 8), (9, 504), (5, 256), (3, 384)]
    (codeMat 84) (codeMat 111) (codeMat 412) false
    det84 det111 inv111
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1638_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1638_orbit
  simpa only [lower3] using h

theorem space1639_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (129, 453), (65, 455), (33, 472), (16, 40), (9, 504), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 239) (codeMat 351) false
    det84 det239 inv239
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1639_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1639_orbit
  simpa only [lower3] using h

theorem space1640_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 33, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 199), (129, 197), (64, 3), (33, 248), (16, 40), (9, 216), (5, 256), (3, 384)]
    (codeMat 84) (codeMat 431) (codeMat 477) false
    det84 det431 inv431
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1640_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1640_orbit
  simpa only [lower3] using h

theorem space1641_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (129, 197), (64, 3), (32, 8), (16, 40), (9, 216), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 143) (codeMat 482) false
    det84 det143 inv143
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1641_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1641_orbit
  simpa only [lower3] using h

theorem space1642_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 197), (128, 1), (64, 3), (32, 40), (16, 8), (9, 216), (5, 384), (3, 128)]
    (codeMat 84) (codeMat 271) (codeMat 314) false
    det84 det271 inv271
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1642_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1642_orbit
  simpa only [lower3] using h

theorem space1643_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 454), (129, 453), (65, 455), (33, 496), (16, 40), (9, 504), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 491) (codeMat 375) false
    det84 det491 inv491
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1643_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1643_orbit
  simpa only [lower3] using h

theorem space1644_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (128, 1), (65, 455), (33, 464), (16, 8), (9, 504), (4, 128), (3, 384)]
    (codeMat 84) (codeMat 107) (codeMat 428) false
    det84 det107 inv107
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1644_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1644_orbit
  simpa only [lower3] using h

theorem space1645_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 197), (64, 3), (33, 208), (16, 40), (9, 216), (4, 128), (3, 384)]
    (codeMat 84) (codeMat 171) (codeMat 485) false
    det84 det171 inv171
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1645_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1645_orbit
  simpa only [lower3] using h

theorem space1646_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 33, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 198), (128, 1), (64, 3), (33, 240), (16, 8), (9, 216), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 299) (codeMat 318) false
    det84 det299 inv299
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1646_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1646_orbit
  simpa only [lower3] using h

theorem space1647_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 452), (128, 1), (65, 455), (32, 32), (16, 8), (9, 504), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 331) (codeMat 410) false
    det84 det331 inv331
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1647_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1647_orbit
  simpa only [lower3] using h

theorem space1648_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 196), (129, 197), (64, 3), (32, 32), (16, 40), (9, 216), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 395) (codeMat 474) false
    det84 det395 inv395
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1648_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space1648_orbit
  simpa only [lower3] using h

theorem space1649_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 327), (129, 326), (65, 325), (33, 376), (17, 368), (8, 40), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    det84 det501 inv501
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1649_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1649_orbit
  simpa only [lower3] using h

theorem space1650_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (128, 2), (65, 325), (33, 344), (17, 336), (8, 40), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 117) (codeMat 380) false
    det84 det117 inv117
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1650_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1650_orbit
  simpa only [lower3] using h

theorem space1651_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (129, 70), (64, 1), (33, 88), (17, 112), (8, 8), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 181) (codeMat 423) false
    det84 det181 inv181
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1651_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1651_orbit
  simpa only [lower3] using h

theorem space1652_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 33, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 71), (128, 2), (64, 1), (33, 120), (17, 80), (8, 8), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 309) (codeMat 309) false
    det84 det309 inv309
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1652_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 33, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1652_orbit
  simpa only [lower3] using h

theorem space1653_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (129, 326), (65, 325), (32, 8), (17, 368), (8, 40), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    det84 det213 inv213
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1653_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1653_orbit
  simpa only [lower3] using h

theorem space1654_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 32, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 69), (129, 70), (64, 1), (32, 40), (17, 112), (8, 8), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 405) (codeMat 407) false
    det84 det405 inv405
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1654_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1654_orbit
  simpa only [lower3] using h

theorem space1655_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 326), (65, 325), (33, 336), (17, 368), (8, 40), (4, 128), (2, 384)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    det84 det241 inv241
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1655_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1655_orbit
  simpa only [lower3] using h

theorem space1656_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 326), (128, 2), (65, 325), (33, 368), (17, 336), (8, 40), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 369) (codeMat 377) false
    det84 det369 inv369
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1656_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1656_orbit
  simpa only [lower3] using h

theorem space1657_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 324), (129, 326), (65, 325), (32, 32), (17, 368), (8, 40), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 465) (codeMat 465) false
    det84 det465 inv465
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1657_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1657_orbit
  simpa only [lower3] using h

theorem space1658_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 64, 32, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 68), (128, 2), (64, 1), (32, 32), (17, 80), (8, 8), (4, 256), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    det84 det273 inv273
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1658_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space1658_orbit
  simpa only [lower3] using h

theorem space1659_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 130, 64, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (130, 455), (64, 2), (34, 472), (18, 504), (10, 464), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 190) (codeMat 355) false
    det84 det190 inv190
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1659_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1659_orbit
  simpa only [lower3] using h

theorem space1660_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 199), (128, 3), (64, 2), (34, 248), (18, 216), (10, 208), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 318) (codeMat 299) false
    det84 det318 inv318
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1660_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1660_orbit
  simpa only [lower3] using h

theorem space1661_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 130, 66, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (130, 455), (66, 454), (34, 464), (18, 504), (10, 496), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 250) (codeMat 397) false
    det84 det250 inv250
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1661_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1661_orbit
  simpa only [lower3] using h

theorem space1662_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 454), (130, 455), (64, 2), (34, 496), (18, 504), (10, 464), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 442) (codeMat 334) false
    det84 det442 inv442
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1662_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1662_orbit
  simpa only [lower3] using h

theorem space1663_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 66, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 452), (130, 455), (66, 454), (32, 32), (18, 504), (10, 496), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 474) (codeMat 395) false
    det84 det474 inv474
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space1663_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space1663_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
