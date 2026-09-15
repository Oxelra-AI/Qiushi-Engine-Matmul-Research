import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1728_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [386, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(386, 139), (20, 10), (10, 30)]
    (codeMat 474) (codeMat 87) (codeMat 468) false
    det474 det87 inv87
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1728_lower : 18 ≤ frozenWangTable.L0 (spanCodes [386, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1728_orbit
  simpa only [lower455] using h

theorem space1729_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [387, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(387, 139), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    det403 det465 inv465
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1729_lower : 18 ≤ frozenWangTable.L0 (spanCodes [387, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1729_orbit
  simpa only [lower455] using h

theorem space1730_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [388, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(388, 139), (20, 10), (10, 30)]
    (codeMat 410) (codeMat 87) (codeMat 468) false
    det410 det87 inv87
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1730_lower : 18 ≤ frozenWangTable.L0 (spanCodes [388, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1730_orbit
  simpa only [lower455] using h

theorem space1731_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [389, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(389, 139), (20, 20), (10, 30)]
    (codeMat 467) (codeMat 465) (codeMat 465) false
    det467 det465 inv465
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1731_lower : 18 ≤ frozenWangTable.L0 (spanCodes [389, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1731_orbit
  simpa only [lower455] using h

theorem space1732_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [391, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(391, 191), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    det275 det465 inv465
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1732_lower : 18 ≤ frozenWangTable.L0 (spanCodes [391, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1732_orbit
  simpa only [lower456] using h

theorem space1733_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [416, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(416, 129), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    det282 det87 inv87
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1733_lower : 18 ≤ frozenWangTable.L0 (spanCodes [416, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1733_orbit
  simpa only [lower455] using h

theorem space1734_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [417, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(417, 159), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    det339 det465 inv465
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1734_lower : 18 ≤ frozenWangTable.L0 (spanCodes [417, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1734_orbit
  simpa only [lower455] using h

theorem space1735_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [419, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(419, 171), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    det403 det465 inv465
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1735_lower : 18 ≤ frozenWangTable.L0 (spanCodes [419, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1735_orbit
  simpa only [lower456] using h

theorem space1736_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [421, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(421, 171), (20, 20), (10, 30)]
    (codeMat 467) (codeMat 465) (codeMat 465) false
    det467 det465 inv465
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space1736_lower : 18 ≤ frozenWangTable.L0 (spanCodes [421, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space1736_orbit
  simpa only [lower456] using h

theorem space1737_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [422, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(422, 129), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    det346 det87 inv87
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1737_lower : 18 ≤ frozenWangTable.L0 (spanCodes [422, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1737_orbit
  simpa only [lower455] using h

theorem space1738_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [423, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(423, 159), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    det275 det465 inv465
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space1738_lower : 18 ≤ frozenWangTable.L0 (spanCodes [423, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space1738_orbit
  simpa only [lower455] using h

theorem space1739_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [449, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(449, 449), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space1739_lower : 18 ≤ frozenWangTable.L0 (spanCodes [449, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space1739_orbit
  simpa only [lower457] using h

theorem space1740_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [450, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(450, 450), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1740_lower : 18 ≤ frozenWangTable.L0 (spanCodes [450, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1740_orbit
  simpa only [lower458] using h

theorem space1741_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [451, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(451, 450), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1741_lower : 18 ≤ frozenWangTable.L0 (spanCodes [451, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1741_orbit
  simpa only [lower458] using h

theorem space1742_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [452, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(452, 456), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1742_lower : 18 ≤ frozenWangTable.L0 (spanCodes [452, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1742_orbit
  simpa only [lower458] using h

theorem space1743_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [453, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(453, 456), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1743_lower : 18 ≤ frozenWangTable.L0 (spanCodes [453, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1743_orbit
  simpa only [lower458] using h

theorem space1744_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [454, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(454, 449), (20, 20), (10, 10)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    det337 det273 inv273
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space1744_lower : 18 ≤ frozenWangTable.L0 (spanCodes [454, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space1744_orbit
  simpa only [lower457] using h

theorem space1745_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [480, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(480, 449), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space1745_lower : 18 ≤ frozenWangTable.L0 (spanCodes [480, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space1745_orbit
  simpa only [lower457] using h

theorem space1746_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [482, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(482, 470), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    det275 det465 inv465
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1746_lower : 18 ≤ frozenWangTable.L0 (spanCodes [482, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1746_orbit
  simpa only [lower458] using h

theorem space1747_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [483, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(483, 456), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    det346 det87 inv87
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1747_lower : 18 ≤ frozenWangTable.L0 (spanCodes [483, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1747_orbit
  simpa only [lower458] using h

theorem space1748_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [484, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(484, 456), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    det282 det87 inv87
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1748_lower : 18 ≤ frozenWangTable.L0 (spanCodes [484, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1748_orbit
  simpa only [lower458] using h

theorem space1749_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [485, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(485, 470), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    det339 det465 inv465
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space1749_lower : 18 ≤ frozenWangTable.L0 (spanCodes [485, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space1749_orbit
  simpa only [lower458] using h

theorem space1750_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [487, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(487, 469), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    det267 det468 inv468
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space1750_lower : 18 ≤ frozenWangTable.L0 (spanCodes [487, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space1750_orbit
  simpa only [lower457] using h

theorem space1751_orbit :
    frozenWangTable.OrbitImage 419 (spanCodes [20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 419 [(20, 43), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 482) (codeMat 143) false
    det281 det482 inv482
    (by rw [basis419]; decide +kernel)
    (by rw [basis419]; decide +kernel)

theorem space1751_lower : 17 ≤ frozenWangTable.L0 (spanCodes [20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 419 space1751_orbit
  simpa only [lower419] using h

theorem space1752_orbit :
    frozenWangTable.OrbitImage 427 (spanCodes [18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 427 [(18, 36), (10, 37), (6, 16)]
    (codeMat 266) (codeMat 481) (codeMat 185) false
    det266 det481 inv481
    (by rw [basis427]; decide +kernel)
    (by rw [basis427]; decide +kernel)

theorem space1752_lower : 17 ≤ frozenWangTable.L0 (spanCodes [18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 427 space1752_orbit
  simpa only [lower427] using h

theorem space1753_orbit :
    frozenWangTable.OrbitImage 419 (spanCodes [36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 419 [(36, 32), (20, 33), (10, 43)]
    (codeMat 282) (codeMat 458) (codeMat 458) false
    det282 det458 inv458
    (by rw [basis419]; decide +kernel)
    (by rw [basis419]; decide +kernel)

theorem space1753_lower : 17 ≤ frozenWangTable.L0 (spanCodes [36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 419 space1753_orbit
  simpa only [lower419] using h

theorem space1754_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [322, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(322, 283), (34, 11), (20, 10), (10, 43)]
    (codeMat 275) (codeMat 122) (codeMat 460) false
    det275 det122 inv122
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space1754_lower : 17 ≤ frozenWangTable.L0 (spanCodes [322, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space1754_orbit
  simpa only [lower295] using h

theorem space1755_orbit :
    frozenWangTable.OrbitImage 447 (spanCodes [448, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 447 [(448, 1), (20, 160), (10, 402)]
    (codeMat 84) (codeMat 233) (codeMat 233) true
    det84 det233 inv233
    (by rw [basis447]; decide +kernel)
    (by rw [basis447]; decide +kernel)

theorem space1755_lower : 17 ≤ frozenWangTable.L0 (spanCodes [448, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 447 space1755_orbit
  simpa only [lower447] using h

theorem space1756_orbit :
    frozenWangTable.OrbitImage 251 (spanCodes [20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 251 [(20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis251]; decide +kernel)
    (by rw [basis251]; decide +kernel)

theorem space1756_lower : 16 ≤ frozenWangTable.L0 (spanCodes [20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 251 space1756_orbit
  simpa only [lower251] using h

theorem space1757_orbit :
    frozenWangTable.OrbitImage 251 (spanCodes [34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 251 [(34, 20), (17, 30), (10, 29), (5, 8)]
    (codeMat 267) (codeMat 465) (codeMat 465) false
    det267 det465 inv465
    (by rw [basis251]; decide +kernel)
    (by rw [basis251]; decide +kernel)

theorem space1757_lower : 16 ≤ frozenWangTable.L0 (spanCodes [34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 251 space1757_orbit
  simpa only [lower251] using h

theorem space1758_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [64, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(64, 2), (20, 264), (8, 1), (2, 32)]
    (codeMat 98) (codeMat 273) (codeMat 273) true
    det98 det273 inv273
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1758_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space1758_orbit
  simpa only [lower269] using h

theorem space1759_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [65, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(65, 2), (20, 297), (9, 1), (3, 32)]
    (codeMat 107) (codeMat 279) (codeMat 279) true
    det107 det279 inv279
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1759_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space1759_orbit
  simpa only [lower269] using h


end QiushiMatmul.FrozenWang
