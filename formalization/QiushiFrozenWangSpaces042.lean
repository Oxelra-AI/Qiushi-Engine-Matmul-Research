import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1344_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 131, 64, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 128), (131, 232), (64, 384), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 270) (codeMat 122) (codeMat 460) false
    det270 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1344_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1344_orbit
  simpa only [lower14] using h

theorem space1345_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (67, 387), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 340) (codeMat 87) (codeMat 468) false
    det340 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1345_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1345_orbit
  simpa only [lower14] using h

theorem space1346_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 10), (130, 3), (67, 30), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 461) (codeMat 122) (codeMat 460) false
    det461 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1346_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1346_orbit
  simpa only [lower14] using h

theorem space1347_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 385), (129, 387), (65, 384), (34, 381), (19, 235), (10, 373), (6, 130)]
    (codeMat 340) (codeMat 494) (codeMat 501) false
    det340 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1347_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1347_orbit
  simpa only [lower14] using h

theorem space1348_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 1), (128, 3), (65, 384), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 348) (codeMat 94) (codeMat 500) false
    det348 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1348_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1348_orbit
  simpa only [lower14] using h

theorem space1349_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 136), (131, 232), (64, 360), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 334) (codeMat 115) (codeMat 492) false
    det334 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1349_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1349_orbit
  simpa only [lower14] using h

theorem space1350_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 480), (130, 384), (64, 360), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 335) (codeMat 501) (codeMat 494) false
    det335 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1350_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1350_orbit
  simpa only [lower14] using h

theorem space1351_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 9), (130, 384), (67, 374), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 351) (codeMat 157) (codeMat 486) false
    det351 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1351_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1351_orbit
  simpa only [lower14] using h

theorem space1352_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 383), (129, 246), (66, 374), (34, 381), (19, 414), (10, 373), (6, 511)]
    (codeMat 342) (codeMat 171) (codeMat 485) false
    det342 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1352_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1352_orbit
  simpa only [lower14] using h

theorem space1353_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 130, 70, 36, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (130, 2), (70, 324), (36, 24), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 116) (codeMat 92) false
    det93 det116 inv116
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1353_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 70, 36, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1353_orbit
  simpa only [lower10] using h

theorem space1354_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 66, 38, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (128, 9), (66, 82), (38, 112), (18, 8), (10, 208), (1, 128)]
    (codeMat 95) (codeMat 298) (codeMat 270) false
    det95 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1354_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 38, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1354_orbit
  simpa only [lower11] using h

theorem space1355_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 70, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 130), (130, 9), (70, 413), (32, 128), (18, 8), (10, 264), (1, 360)]
    (codeMat 158) (codeMat 99) (codeMat 172) false
    det158 det99 inv99
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1355_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 70, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space1355_orbit
  simpa only [lower14] using h

theorem space1356_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [262, 130, 64, 32, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(262, 196), (130, 3), (64, 130), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 85) (codeMat 282) (codeMat 267) false
    det85 det282 inv282
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1356_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 130, 64, 32, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1356_orbit
  simpa only [lower11] using h

theorem space1357_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [262, 134, 70, 34, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(262, 71), (134, 70), (70, 68), (34, 440), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    det84 det500 inv500
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1357_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 70, 34, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1357_orbit
  simpa only [lower10] using h

theorem space1358_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 160, 64, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (160, 70), (64, 2), (18, 432), (10, 176), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 156) (codeMat 102) false
    det140 det156 inv156
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space1358_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space1358_orbit
  simpa only [lower10] using h

theorem space1359_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [290, 128, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(290, 60), (128, 219), (66, 81), (18, 216), (10, 88), (4, 32), (1, 8)]
    (codeMat 143) (codeMat 275) (codeMat 275) false
    det143 det275 inv275
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1359_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 128, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1359_orbit
  simpa only [lower11] using h

theorem space1360_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 194, 32, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 112), (194, 240), (32, 1), (18, 54), (10, 53), (4, 8), (1, 40)]
    (codeMat 266) (codeMat 213) (codeMat 470) false
    det266 det213 inv213
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1360_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 194, 32, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1360_orbit
  simpa only [lower11] using h

theorem space1361_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [322, 128, 34, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(322, 80), (128, 128), (34, 52), (18, 2), (10, 61), (4, 32), (1, 40)]
    (codeMat 267) (codeMat 337) (codeMat 337) false
    det267 det337 inv337
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1361_lower : 12 ≤ frozenWangTable.L0 (spanCodes [322, 128, 34, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1361_orbit
  simpa only [lower11] using h

theorem space1362_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [288, 128, 66, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(288, 54), (128, 219), (66, 81), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 143) (codeMat 307) (codeMat 311) false
    det143 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1362_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 128, 66, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1362_orbit
  simpa only [lower11] using h

theorem space1363_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 194, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (194, 240), (32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    det266 det241 inv241
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1363_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 194, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1363_orbit
  simpa only [lower11] using h

theorem space1364_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [320, 130, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(320, 128), (130, 216), (32, 54), (18, 3), (10, 60), (6, 40), (1, 32)]
    (codeMat 267) (codeMat 370) (codeMat 207) false
    det267 det370 inv370
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1364_lower : 12 ≤ frozenWangTable.L0 (spanCodes [320, 130, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1364_orbit
  simpa only [lower11] using h

theorem space1365_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [386, 64, 32, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(386, 199), (64, 128), (32, 32), (18, 63), (10, 23), (6, 3), (1, 2)]
    (codeMat 273) (codeMat 410) (codeMat 331) false
    det273 det410 inv410
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1365_lower : 12 ≤ frozenWangTable.L0 (spanCodes [386, 64, 32, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1365_orbit
  simpa only [lower11] using h

theorem space1366_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [386, 66, 34, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(386, 71), (66, 199), (34, 55), (18, 63), (10, 31), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 443) (codeMat 254) false
    det273 det443 inv443
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space1366_lower : 12 ≤ frozenWangTable.L0 (spanCodes [386, 66, 34, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space1366_orbit
  simpa only [lower11] using h

theorem space1367_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 3), (66, 29), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 460) (codeMat 115) (codeMat 492) false
    det460 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1367_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1367_orbit
  simpa only [lower14] using h

theorem space1368_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 23), (129, 30), (66, 29), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 461) (codeMat 501) (codeMat 494) false
    det461 det501 inv501
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1368_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1368_orbit
  simpa only [lower14] using h

theorem space1369_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 252), (130, 360), (67, 245), (34, 381), (19, 235), (10, 373), (6, 130)]
    (codeMat 470) (codeMat 494) (codeMat 501) false
    det470 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1369_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1369_orbit
  simpa only [lower14] using h

theorem space1370_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 139), (131, 413), (67, 245), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 478) (codeMat 94) (codeMat 500) false
    det478 det94 inv94
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1370_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1370_orbit
  simpa only [lower14] using h

theorem space1371_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (130, 360), (64, 3), (34, 381), (19, 414), (10, 373), (6, 511)]
    (codeMat 468) (codeMat 171) (codeMat 485) false
    det468 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1371_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1371_orbit
  simpa only [lower14] using h

theorem space1372_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 510), (129, 363), (65, 3), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 477) (codeMat 157) (codeMat 486) false
    det477 det157 inv157
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1372_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1372_orbit
  simpa only [lower14] using h

theorem space1373_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 130, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (130, 360), (66, 363), (32, 130), (19, 414), (10, 235), (6, 511)]
    (codeMat 412) (codeMat 234) (codeMat 461) false
    det412 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1373_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1373_orbit
  simpa only [lower14] using h

theorem space1374_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 502), (128, 384), (66, 246), (32, 8), (19, 235), (10, 414), (6, 511)]
    (codeMat 279) (codeMat 213) (codeMat 470) false
    det279 det213 inv213
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1374_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1374_orbit
  simpa only [lower14] using h

theorem space1375_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 252), (130, 360), (67, 413), (32, 511), (19, 235), (10, 414), (6, 130)]
    (codeMat 415) (codeMat 431) (codeMat 477) false
    det415 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space1375_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space1375_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
