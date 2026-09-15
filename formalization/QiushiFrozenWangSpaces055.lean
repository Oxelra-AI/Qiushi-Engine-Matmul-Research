import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space1760_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [64, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(64, 2), (20, 297), (9, 1), (3, 32)]
    (codeMat 99) (codeMat 279) (codeMat 279) true
    det99 det279 inv279
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1760_lower : 16 ≤ frozenWangTable.L0 (spanCodes [64, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space1760_orbit
  simpa only [lower269] using h

theorem space1761_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [65, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(65, 2), (20, 264), (8, 1), (2, 32)]
    (codeMat 106) (codeMat 273) (codeMat 273) true
    det106 det273 inv273
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1761_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space1761_orbit
  simpa only [lower269] using h

theorem space1762_orbit :
    frozenWangTable.OrbitImage 264 (spanCodes [128, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 264 [(128, 2), (20, 12), (8, 256), (2, 1)]
    (codeMat 161) (codeMat 98) (codeMat 140) true
    det161 det98 inv98
    (by rw [basis264]; decide +kernel)
    (by rw [basis264]; decide +kernel)

theorem space1762_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 264 space1762_orbit
  simpa only [lower264] using h

theorem space1763_orbit :
    frozenWangTable.OrbitImage 324 (spanCodes [130, 66, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 324 [(130, 1), (66, 17), (20, 197), (10, 53)]
    (codeMat 421) (codeMat 271) (codeMat 314) true
    det421 det271 inv271
    (by rw [basis324]; decide +kernel)
    (by rw [basis324]; decide +kernel)

theorem space1763_lower : 16 ≤ frozenWangTable.L0 (spanCodes [130, 66, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 324 space1763_orbit
  simpa only [lower324] using h

theorem space1764_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [256, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(256, 2), (16, 32), (10, 264), (4, 1)]
    (codeMat 161) (codeMat 84) (codeMat 84) true
    det161 det84 inv84
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1764_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 269 space1764_orbit
  simpa only [lower269] using h

theorem space1765_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [260, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(260, 2), (36, 1), (20, 33), (10, 297)]
    (codeMat 171) (codeMat 87) (codeMat 468) true
    det171 det87 inv87
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1765_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space1765_orbit
  simpa only [lower269] using h

theorem space1766_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [256, 36, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(256, 2), (36, 1), (20, 33), (10, 297)]
    (codeMat 163) (codeMat 87) (codeMat 468) true
    det163 det87 inv87
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1766_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 36, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space1766_orbit
  simpa only [lower269] using h

theorem space1767_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [288, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(288, 2), (16, 32), (10, 264), (4, 1)]
    (codeMat 177) (codeMat 84) (codeMat 84) true
    det177 det84 inv84
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1767_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 269 space1767_orbit
  simpa only [lower269] using h

theorem space1768_orbit :
    frozenWangTable.OrbitImage 96 (spanCodes [258, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 96 [(258, 80), (32, 1), (16, 2), (10, 20), (4, 8)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis96]; decide +kernel)
    (by rw [basis96]; decide +kernel)

theorem space1768_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 96 space1768_orbit
  simpa only [lower96] using h

theorem space1769_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [256, 64, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(256, 1), (64, 2), (20, 96), (10, 272)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    det84 det140 inv140
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space1769_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 64, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space1769_orbit
  simpa only [lower276] using h

theorem space1770_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [260, 65, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(260, 1), (65, 2), (20, 96), (10, 272)]
    (codeMat 85) (codeMat 140) (codeMat 98) false
    det85 det140 inv140
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space1770_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 65, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space1770_orbit
  simpa only [lower276] using h

theorem space1771_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [320, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(320, 2), (17, 296), (10, 264), (5, 1)]
    (codeMat 225) (codeMat 468) (codeMat 87) true
    det225 det468 inv468
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1771_lower : 16 ≤ frozenWangTable.L0 (spanCodes [320, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 269 space1771_orbit
  simpa only [lower269] using h

theorem space1772_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [320, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(320, 2), (34, 296), (20, 264), (10, 297)]
    (codeMat 226) (codeMat 465) (codeMat 465) true
    det226 det465 inv465
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1772_lower : 16 ≤ frozenWangTable.L0 (spanCodes [320, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space1772_orbit
  simpa only [lower269] using h

theorem space1773_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [325, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(325, 2), (34, 296), (20, 264), (10, 297)]
    (codeMat 234) (codeMat 465) (codeMat 465) true
    det234 det465 inv465
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1773_lower : 16 ≤ frozenWangTable.L0 (spanCodes [325, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 269 space1773_orbit
  simpa only [lower269] using h

theorem space1774_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [262, 65, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(262, 264), (65, 16), (32, 1), (20, 68), (10, 258)]
    (codeMat 106) (codeMat 140) (codeMat 98) false
    det106 det140 inv140
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1774_lower : 16 ≤ frozenWangTable.L0 (spanCodes [262, 65, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1774_orbit
  simpa only [lower150] using h

theorem space1775_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [354, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(354, 266), (17, 296), (10, 264), (5, 1)]
    (codeMat 241) (codeMat 468) (codeMat 87) true
    det241 det468 inv468
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space1775_lower : 16 ≤ frozenWangTable.L0 (spanCodes [354, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 269 space1775_orbit
  simpa only [lower269] using h

theorem space1776_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [288, 70, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(288, 16), (70, 78), (20, 258), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 161) (codeMat 161) false
    det177 det161 inv161
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1776_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 70, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 150 space1776_orbit
  simpa only [lower150] using h

theorem space1777_orbit :
    frozenWangTable.OrbitImage 324 (spanCodes [260, 132, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 324 [(260, 36), (132, 52), (20, 53), (10, 197)]
    (codeMat 358) (codeMat 103) (codeMat 188) true
    det358 det103 inv103
    (by rw [basis324]; decide +kernel)
    (by rw [basis324]; decide +kernel)

theorem space1777_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 132, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 324 space1777_orbit
  simpa only [lower324] using h

theorem space1778_orbit :
    frozenWangTable.OrbitImage 324 (spanCodes [354, 192, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 324 [(354, 212), (192, 16), (20, 197), (10, 240)]
    (codeMat 423) (codeMat 460) (codeMat 122) true
    det423 det460 inv460
    (by rw [basis324]; decide +kernel)
    (by rw [basis324]; decide +kernel)

theorem space1778_lower : 16 ≤ frozenWangTable.L0 (spanCodes [354, 192, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 324 space1778_orbit
  simpa only [lower324] using h

theorem space1779_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [256, 192, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(256, 1), (192, 2), (20, 96), (10, 304)]
    (codeMat 84) (codeMat 204) (codeMat 114) false
    det84 det204 inv204
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1779_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 192, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1779_orbit
  simpa only [lower278] using h

theorem space1780_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [320, 128, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(320, 1), (128, 2), (20, 336), (10, 304)]
    (codeMat 92) (codeMat 380) (codeMat 117) false
    det92 det380 inv380
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1780_lower : 16 ≤ frozenWangTable.L0 (spanCodes [320, 128, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1780_orbit
  simpa only [lower278] using h

theorem space1781_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [384, 64, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(384, 2), (64, 1), (20, 304), (10, 96)]
    (codeMat 140) (codeMat 417) (codeMat 177) false
    det140 det417 inv417
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1781_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 64, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1781_orbit
  simpa only [lower278] using h

theorem space1782_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [448, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(448, 384), (20, 42), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 486) (codeMat 157) false
    det281 det486 inv486
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space1782_lower : 16 ≤ frozenWangTable.L0 (spanCodes [448, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 298 space1782_orbit
  simpa only [lower298] using h

theorem space1783_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 195, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 1), (195, 2), (20, 96), (10, 304)]
    (codeMat 85) (codeMat 204) (codeMat 114) false
    det85 det204 inv204
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1783_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 195, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1783_orbit
  simpa only [lower278] using h

theorem space1784_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [325, 130, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(325, 1), (130, 2), (20, 336), (10, 304)]
    (codeMat 93) (codeMat 380) (codeMat 117) false
    det93 det380 inv380
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1784_lower : 16 ≤ frozenWangTable.L0 (spanCodes [325, 130, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1784_orbit
  simpa only [lower278] using h

theorem space1785_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [390, 65, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(390, 2), (65, 1), (20, 304), (10, 96)]
    (codeMat 141) (codeMat 417) (codeMat 177) false
    det141 det417 inv417
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1785_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 65, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1785_orbit
  simpa only [lower278] using h

theorem space1786_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [262, 198, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(262, 264), (198, 280), (32, 1), (20, 69), (10, 326)]
    (codeMat 98) (codeMat 206) (codeMat 498) false
    det98 det206 inv206
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1786_lower : 16 ≤ frozenWangTable.L0 (spanCodes [262, 198, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1786_orbit
  simpa only [lower150] using h

theorem space1787_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [292, 197, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(292, 1), (197, 338), (20, 96), (10, 304)]
    (codeMat 87) (codeMat 204) (codeMat 114) false
    det87 det204 inv204
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1787_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 197, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1787_orbit
  simpa only [lower278] using h

theorem space1788_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [359, 134, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(359, 305), (134, 338), (20, 336), (10, 304)]
    (codeMat 95) (codeMat 380) (codeMat 117) false
    det95 det380 inv380
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1788_lower : 16 ≤ frozenWangTable.L0 (spanCodes [359, 134, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1788_orbit
  simpa only [lower278] using h

theorem space1789_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [418, 67, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(418, 306), (67, 97), (20, 304), (10, 96)]
    (codeMat 143) (codeMat 417) (codeMat 177) false
    det143 det417 inv417
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1789_lower : 16 ≤ frozenWangTable.L0 (spanCodes [418, 67, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1789_orbit
  simpa only [lower278] using h

theorem space1790_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [258, 195, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(258, 264), (195, 16), (32, 1), (20, 69), (10, 327)]
    (codeMat 106) (codeMat 207) (codeMat 370) false
    det106 det207 inv207
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space1790_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 195, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space1790_orbit
  simpa only [lower150] using h

theorem space1791_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [288, 198, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(288, 1), (198, 338), (20, 96), (10, 304)]
    (codeMat 86) (codeMat 204) (codeMat 114) false
    det86 det204 inv204
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space1791_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 198, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space1791_orbit
  simpa only [lower278] using h


end QiushiMatmul.FrozenWang
