import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1536_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (129, 246), (64, 384), (32, 130), (19, 414), (10, 235), (6, 511)]
    (codeMat 286) (codeMat 234) (codeMat 461) false
    det286 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1536_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1536_orbit
  simpa only [lower14] using h

theorem space1537_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 20), (129, 30), (66, 29), (35, 284), (19, 414), (10, 373), (5, 8)]
    (codeMat 461) (codeMat 465) (codeMat 465) false
    det461 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1537_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1537_orbit
  simpa only [lower14] using h

theorem space1538_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 66, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 483), (128, 360), (66, 245), (35, 227), (19, 235), (10, 373), (5, 130)]
    (codeMat 407) (codeMat 458) (codeMat 458) false
    det407 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1538_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1538_orbit
  simpa only [lower14] using h

theorem space1539_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 386), (129, 387), (65, 384), (35, 227), (19, 235), (10, 373), (5, 130)]
    (codeMat 340) (codeMat 458) (codeMat 458) false
    det340 det458 inv458
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1539_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1539_orbit
  simpa only [lower14] using h

theorem space1540_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 256), (128, 384), (65, 360), (35, 284), (19, 414), (10, 373), (5, 8)]
    (codeMat 270) (codeMat 465) (codeMat 465) false
    det270 det465 inv465
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1540_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1540_orbit
  simpa only [lower14] using h

theorem space1541_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (67, 232), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 271) (codeMat 185) (codeMat 481) false
    det271 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1541_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1541_orbit
  simpa only [lower14] using h

theorem space1542_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 139), (128, 360), (66, 413), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 478) (codeMat 143) (codeMat 482) false
    det478 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1542_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1542_orbit
  simpa only [lower14] using h

theorem space1543_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 10), (131, 30), (65, 3), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 397) (codeMat 185) (codeMat 481) false
    det397 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1543_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1543_orbit
  simpa only [lower14] using h

theorem space1544_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (131, 387), (64, 3), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 348) (codeMat 143) (codeMat 482) false
    det348 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1544_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1544_orbit
  simpa only [lower14] using h

theorem space1545_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 136), (128, 360), (67, 232), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 335) (codeMat 171) (codeMat 485) false
    det335 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1545_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1545_orbit
  simpa only [lower14] using h

theorem space1546_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 385), (130, 384), (66, 387), (32, 511), (19, 373), (10, 235), (5, 130)]
    (codeMat 348) (codeMat 501) (codeMat 494) false
    det348 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1546_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1546_orbit
  simpa only [lower14] using h

theorem space1547_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 383), (129, 374), (66, 246), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 351) (codeMat 115) (codeMat 492) false
    det351 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1547_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1547_orbit
  simpa only [lower14] using h

theorem space1548_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (131, 374), (65, 384), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 342) (codeMat 94) (codeMat 500) false
    det342 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1548_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1548_orbit
  simpa only [lower14] using h

theorem space1549_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 480), (128, 360), (65, 384), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 334) (codeMat 494) (codeMat 501) false
    det334 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1549_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1549_orbit
  simpa only [lower14] using h

theorem space1550_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (130, 384), (64, 3), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 340) (codeMat 157) (codeMat 486) false
    det340 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1550_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space1550_orbit
  simpa only [lower14] using h

theorem space1551_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 67, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 104), (128, 384), (67, 232), (35, 97), (19, 414), (10, 235), (4, 8)]
    (codeMat 271) (codeMat 157) (codeMat 486) false
    det271 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1551_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1551_orbit
  simpa only [lower14] using h

theorem space1552_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (130, 3), (66, 387), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 277) (codeMat 115) (codeMat 492) false
    det277 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1552_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1552_orbit
  simpa only [lower14] using h

theorem space1553_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 118), (128, 384), (66, 246), (35, 227), (19, 235), (10, 414), (4, 511)]
    (codeMat 279) (codeMat 501) (codeMat 494) false
    det279 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1553_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1553_orbit
  simpa only [lower14] using h

theorem space1554_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 65, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (129, 387), (65, 3), (35, 276), (19, 235), (10, 414), (4, 130)]
    (codeMat 285) (codeMat 171) (codeMat 485) false
    det285 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1554_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1554_orbit
  simpa only [lower14] using h

theorem space1555_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 104), (131, 232), (64, 384), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 270) (codeMat 94) (codeMat 500) false
    det270 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1555_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1555_orbit
  simpa only [lower14] using h

theorem space1556_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 64, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 118), (129, 246), (64, 384), (35, 284), (19, 414), (10, 235), (4, 511)]
    (codeMat 286) (codeMat 494) (codeMat 501) false
    det286 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1556_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1556_orbit
  simpa only [lower14] using h

theorem space1557_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 67, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 96), (128, 360), (67, 232), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 335) (codeMat 143) (codeMat 482) false
    det335 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1557_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 67, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1557_orbit
  simpa only [lower14] using h

theorem space1558_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 404), (129, 245), (66, 413), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 470) (codeMat 185) (codeMat 481) false
    det470 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1558_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1558_orbit
  simpa only [lower14] using h

theorem space1559_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (128, 384), (65, 3), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 277) (codeMat 185) (codeMat 481) false
    det277 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1559_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1559_orbit
  simpa only [lower14] using h

theorem space1560_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 129, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (129, 29), (64, 3), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 396) (codeMat 143) (codeMat 482) false
    det396 det143 inv143
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1560_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1560_orbit
  simpa only [lower14] using h

theorem space1561_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 404), (129, 413), (66, 245), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 415) (codeMat 122) (codeMat 460) false
    det415 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1561_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1561_orbit
  simpa only [lower14] using h

theorem space1562_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (66, 29), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 460) (codeMat 87) (codeMat 468) false
    det460 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1562_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1562_orbit
  simpa only [lower14] using h

theorem space1563_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 96), (131, 232), (64, 360), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 334) (codeMat 87) (codeMat 468) false
    det334 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1563_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1563_orbit
  simpa only [lower14] using h

theorem space1564_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (130, 3), (64, 384), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 285) (codeMat 122) (codeMat 460) false
    det285 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1564_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space1564_orbit
  simpa only [lower14] using h

theorem space1565_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 68, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (133, 373), (68, 284), (37, 480), (16, 360), (9, 256), (3, 8)]
    (codeMat 206) (codeMat 486) (codeMat 157) false
    det206 det486 inv486
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1565_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 68, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space1565_orbit
  simpa only [lower14] using h

theorem space1566_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 37, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (128, 3), (64, 1), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 92) (codeMat 307) (codeMat 311) false
    det92 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1566_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 37, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space1566_orbit
  simpa only [lower11] using h

theorem space1567_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 133, 65, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (133, 326), (65, 2), (36, 8), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 156) (codeMat 102) false
    det93 det156 inv156
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1567_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space1567_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
