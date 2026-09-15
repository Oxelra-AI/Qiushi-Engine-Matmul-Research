import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2400_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 84, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 1), (84, 337), (32, 2), (10, 306)]
    (codeMat 213) (codeMat 213) (codeMat 470) true
    det213 det213 inv213
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2400_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 84, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2400_orbit
  simpa only [lower278] using h

theorem space2401_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [273, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(273, 98), (84, 114), (53, 322), (10, 323)]
    (codeMat 171) (codeMat 346) (codeMat 459) false
    det171 det346 inv346
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2401_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2401_orbit
  simpa only [lower338] using h

theorem space2402_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [276, 84, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(276, 289), (84, 305), (48, 1), (10, 323)]
    (codeMat 226) (codeMat 458) (codeMat 458) false
    det226 det458 inv458
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2402_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 84, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2402_orbit
  simpa only [lower338] using h

theorem space2403_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [288, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(288, 2), (80, 304), (10, 96), (4, 1)]
    (codeMat 177) (codeMat 140) (codeMat 98) true
    det177 det140 inv140
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2403_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 278 space2403_orbit
  simpa only [lower278] using h

theorem space2404_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [259, 64, 39, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(259, 280), (64, 16), (39, 259), (20, 326), (10, 258)]
    (codeMat 99) (codeMat 188) (codeMat 103) false
    det99 det188 inv188
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2404_lower : 16 ≤ frozenWangTable.L0 (spanCodes [259, 64, 39, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2404_orbit
  simpa only [lower150] using h

theorem space2405_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [262, 65, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(262, 280), (65, 16), (34, 259), (21, 68), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    det106 det172 inv172
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2405_lower : 16 ≤ frozenWangTable.L0 (spanCodes [262, 65, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2405_orbit
  simpa only [lower150] using h

theorem space2406_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [292, 67, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(292, 3), (67, 97), (23, 304), (10, 96)]
    (codeMat 143) (codeMat 165) (codeMat 163) false
    det143 det165 inv165
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2406_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 67, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2406_orbit
  simpa only [lower278] using h

theorem space2407_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [256, 84, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(256, 16), (84, 114), (54, 1), (10, 323)]
    (codeMat 163) (codeMat 122) (codeMat 460) false
    det163 det122 inv122
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2407_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 84, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2407_orbit
  simpa only [lower338] using h

theorem space2408_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [260, 84, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(260, 16), (84, 305), (50, 322), (10, 323)]
    (codeMat 234) (codeMat 234) (codeMat 461) false
    det234 det234 inv234
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2408_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 84, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2408_orbit
  simpa only [lower338] using h

theorem space2409_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [273, 84, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(273, 98), (84, 99), (39, 304), (10, 306)]
    (codeMat 157) (codeMat 339) (codeMat 467) true
    det157 det339 inv339
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2409_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 84, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2409_orbit
  simpa only [lower278] using h

theorem space2410_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 84, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 336), (84, 337), (34, 304), (10, 306)]
    (codeMat 212) (codeMat 465) (codeMat 465) true
    det212 det465 inv465
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2410_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 84, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2410_orbit
  simpa only [lower278] using h

theorem space2411_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [288, 66, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(288, 2), (66, 97), (22, 304), (10, 96)]
    (codeMat 142) (codeMat 161) (codeMat 161) false
    det142 det161 inv161
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2411_lower : 16 ≤ frozenWangTable.L0 (spanCodes [288, 66, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2411_orbit
  simpa only [lower278] using h

theorem space2412_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [258, 64, 32, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(258, 264), (64, 16), (32, 1), (20, 68), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    det98 det140 inv140
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2412_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2412_orbit
  simpa only [lower150] using h

theorem space2413_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [263, 65, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(263, 264), (65, 16), (36, 1), (21, 326), (10, 258)]
    (codeMat 107) (codeMat 156) (codeMat 102) false
    det107 det156 inv156
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2413_lower : 16 ≤ frozenWangTable.L0 (spanCodes [263, 65, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2413_orbit
  simpa only [lower150] using h

theorem space2414_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [307, 81, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(307, 339), (81, 304), (10, 96), (5, 1)]
    (codeMat 185) (codeMat 172) (codeMat 99) true
    det185 det172 inv172
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2414_lower : 16 ≤ frozenWangTable.L0 (spanCodes [307, 81, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 278 space2414_orbit
  simpa only [lower278] using h

theorem space2415_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [256, 134, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(256, 1), (134, 289), (84, 99), (10, 338)]
    (codeMat 244) (codeMat 207) (codeMat 370) false
    det244 det207 inv207
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2415_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 134, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2415_orbit
  simpa only [lower338] using h

theorem space2416_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 130, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 1), (130, 2), (84, 305), (10, 338)]
    (codeMat 181) (codeMat 93) (codeMat 372) false
    det181 det93 inv93
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2416_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 130, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2416_orbit
  simpa only [lower278] using h

theorem space2417_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [273, 151, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(273, 98), (151, 97), (84, 99), (10, 338)]
    (codeMat 253) (codeMat 491) (codeMat 375) false
    det253 det491 inv491
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2417_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 151, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2417_orbit
  simpa only [lower278] using h

theorem space2418_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [276, 146, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(276, 304), (146, 16), (84, 305), (10, 338)]
    (codeMat 188) (codeMat 377) (codeMat 369) false
    det188 det377 inv377
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2418_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 146, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2418_orbit
  simpa only [lower338] using h

theorem space2419_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [384, 82, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(384, 2), (82, 336), (10, 96), (6, 1)]
    (codeMat 161) (codeMat 396) (codeMat 106) true
    det161 det396 inv396
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2419_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 82, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 278 space2419_orbit
  simpa only [lower278] using h

theorem space2420_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [258, 128, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(258, 10), (128, 1), (80, 68), (10, 264), (4, 16)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    det140 det98 inv98
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2420_lower : 16 ≤ frozenWangTable.L0 (spanCodes [258, 128, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 150 space2420_orbit
  simpa only [lower150] using h

theorem space2421_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [274, 145, 81, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(274, 326), (145, 333), (81, 332), (10, 264), (5, 16)]
    (codeMat 204) (codeMat 482) (codeMat 143) false
    det204 det482 inv482
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2421_lower : 16 ≤ frozenWangTable.L0 (spanCodes [274, 145, 81, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 150 space2421_orbit
  simpa only [lower150] using h

theorem space2422_orbit :
    frozenWangTable.OrbitImage 275 (spanCodes [273, 130, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 275 [(273, 85), (130, 2), (84, 84), (10, 160)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    det85 det340 inv340
    (by rw [basis275]; decide +kernel)
    (by rw [basis275]; decide +kernel)

theorem space2422_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 130, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 275 space2422_orbit
  simpa only [lower275] using h

theorem space2423_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [390, 65, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(390, 3), (65, 1), (21, 304), (10, 96)]
    (codeMat 141) (codeMat 421) (codeMat 179) false
    det141 det421 inv421
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2423_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 65, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2423_orbit
  simpa only [lower278] using h

theorem space2424_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [256, 148, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(256, 1), (148, 97), (84, 99), (10, 338)]
    (codeMat 244) (codeMat 207) (codeMat 370) false
    det244 det207 inv207
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2424_lower : 16 ≤ frozenWangTable.L0 (spanCodes [256, 148, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2424_orbit
  simpa only [lower278] using h

theorem space2425_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [260, 144, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(260, 1), (144, 16), (84, 305), (10, 338)]
    (codeMat 181) (codeMat 93) (codeMat 372) false
    det181 det93 inv93
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2425_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 144, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2425_orbit
  simpa only [lower338] using h

theorem space2426_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [273, 133, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(273, 98), (133, 289), (84, 99), (10, 338)]
    (codeMat 253) (codeMat 491) (codeMat 375) false
    det253 det491 inv491
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2426_lower : 16 ≤ frozenWangTable.L0 (spanCodes [273, 133, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2426_orbit
  simpa only [lower338] using h

theorem space2427_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [276, 128, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(276, 304), (128, 2), (84, 305), (10, 338)]
    (codeMat 188) (codeMat 377) (codeMat 369) false
    det188 det377 inv377
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2427_lower : 16 ≤ frozenWangTable.L0 (spanCodes [276, 128, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2427_orbit
  simpa only [lower278] using h

theorem space2428_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [294, 162, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(294, 332), (162, 68), (68, 280), (16, 1), (10, 79)]
    (codeMat 354) (codeMat 331) (codeMat 410) false
    det354 det331 inv331
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2428_lower : 16 ≤ frozenWangTable.L0 (spanCodes [294, 162, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2428_orbit
  simpa only [lower150] using h

theorem space2429_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [292, 161, 69, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(292, 27), (161, 275), (69, 280), (17, 78), (10, 79)]
    (codeMat 355) (codeMat 253) (codeMat 415) false
    det355 det253 inv253
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2429_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 161, 69, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2429_orbit
  simpa only [lower150] using h

theorem space2430_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [259, 147, 80, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(259, 26), (147, 333), (80, 332), (10, 264), (4, 16)]
    (codeMat 205) (codeMat 226) (codeMat 141) false
    det205 det226 inv226
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2430_lower : 16 ≤ frozenWangTable.L0 (spanCodes [259, 147, 80, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 150 space2430_orbit
  simpa only [lower150] using h

theorem space2431_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 130, 81, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 94), (130, 1), (81, 68), (10, 264), (5, 16)]
    (codeMat 141) (codeMat 354) (codeMat 142) false
    det141 det354 inv354
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2431_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 130, 81, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 150 space2431_orbit
  simpa only [lower150] using h


end QiushiMatmul.FrozenWang
