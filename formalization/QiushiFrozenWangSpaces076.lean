import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2432_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [403, 83, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(403, 339), (83, 336), (10, 96), (7, 1)]
    (codeMat 169) (codeMat 428) (codeMat 107) true
    det169 det428 inv428
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2432_lower : 16 ≤ frozenWangTable.L0 (spanCodes [403, 83, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space2432_orbit
  simpa only [lower278] using h

theorem space2433_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [292, 162, 68, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(292, 27), (162, 11), (68, 280), (16, 1), (10, 79)]
    (codeMat 298) (codeMat 111) (codeMat 412) false
    det298 det111 inv111
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2433_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 162, 68, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2433_orbit
  simpa only [lower150] using h

theorem space2434_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [295, 161, 69, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(295, 332), (161, 348), (69, 280), (17, 78), (10, 79)]
    (codeMat 299) (codeMat 473) (codeMat 409) false
    det299 det473 inv473
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2434_lower : 16 ≤ frozenWangTable.L0 (spanCodes [295, 161, 69, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2434_orbit
  simpa only [lower150] using h

theorem space2435_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [292, 133, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(292, 3), (133, 97), (84, 305), (10, 338)]
    (codeMat 239) (codeMat 239) (codeMat 351) false
    det239 det239 inv239
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2435_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 133, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2435_orbit
  simpa only [lower278] using h

theorem space2436_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [310, 151, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(310, 323), (151, 289), (84, 305), (10, 338)]
    (codeMat 239) (codeMat 239) (codeMat 351) false
    det239 det239 inv239
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2436_lower : 16 ≤ frozenWangTable.L0 (spanCodes [310, 151, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2436_orbit
  simpa only [lower338] using h

theorem space2437_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [390, 84, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(390, 288), (84, 305), (39, 322), (10, 323)]
    (codeMat 187) (codeMat 382) (codeMat 499) false
    det187 det382 inv382
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2437_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 84, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2437_orbit
  simpa only [lower338] using h

theorem space2438_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [404, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(404, 338), (84, 337), (53, 304), (10, 306)]
    (codeMat 159) (codeMat 375) (codeMat 491) true
    det159 det375 inv375
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2438_lower : 16 ≤ frozenWangTable.L0 (spanCodes [404, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2438_orbit
  simpa only [lower278] using h

theorem space2439_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [305, 146, 83, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(305, 95), (146, 1), (83, 332), (10, 264), (7, 16)]
    (codeMat 143) (codeMat 358) (codeMat 158) false
    det143 det358 inv358
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2439_lower : 16 ≤ frozenWangTable.L0 (spanCodes [305, 146, 83, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 150 space2439_orbit
  simpa only [lower150] using h

theorem space2440_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [291, 129, 83, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(291, 11), (129, 333), (83, 68), (10, 264), (7, 16)]
    (codeMat 206) (codeMat 230) (codeMat 159) false
    det206 det230 inv230
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2440_lower : 16 ≤ frozenWangTable.L0 (spanCodes [291, 129, 83, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 150 space2440_orbit
  simpa only [lower150] using h

theorem space2441_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [292, 130, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(292, 288), (130, 16), (84, 99), (10, 338)]
    (codeMat 174) (codeMat 345) (codeMat 345) false
    det174 det345 inv345
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2441_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 130, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2441_orbit
  simpa only [lower338] using h

theorem space2442_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [310, 144, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(310, 306), (144, 2), (84, 99), (10, 338)]
    (codeMat 174) (codeMat 345) (codeMat 345) false
    det174 det345 inv345
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2442_lower : 16 ≤ frozenWangTable.L0 (spanCodes [310, 144, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2442_orbit
  simpa only [lower278] using h

theorem space2443_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [390, 84, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(390, 288), (84, 114), (32, 1), (10, 323)]
    (codeMat 242) (codeMat 206) (codeMat 498) false
    det242 det206 inv206
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2443_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 84, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2443_orbit
  simpa only [lower338] using h

theorem space2444_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [404, 84, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(404, 96), (84, 99), (50, 304), (10, 306)]
    (codeMat 214) (codeMat 241) (codeMat 489) true
    det214 det241 inv241
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2444_lower : 16 ≤ frozenWangTable.L0 (spanCodes [404, 84, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2444_orbit
  simpa only [lower278] using h

theorem space2445_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [261, 148, 84, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(261, 197), (148, 191), (84, 190), (54, 16), (10, 112)]
    (codeMat 92) (codeMat 478) (codeMat 445) false
    det92 det478 inv478
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2445_lower : 16 ≤ frozenWangTable.L0 (spanCodes [261, 148, 84, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2445_orbit
  simpa only [lower152] using h

theorem space2446_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [292, 148, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(292, 288), (148, 289), (84, 305), (10, 338)]
    (codeMat 230) (codeMat 459) (codeMat 346) false
    det230 det459 inv459
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2446_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 148, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2446_orbit
  simpa only [lower338] using h

theorem space2447_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [310, 134, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(310, 96), (134, 97), (84, 305), (10, 338)]
    (codeMat 230) (codeMat 459) (codeMat 346) false
    det230 det459 inv459
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2447_lower : 16 ≤ frozenWangTable.L0 (spanCodes [310, 134, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2447_orbit
  simpa only [lower278] using h

theorem space2448_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [390, 84, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(390, 3), (84, 337), (54, 2), (10, 306)]
    (codeMat 158) (codeMat 115) (codeMat 492) true
    det158 det115 inv115
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2448_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 84, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2448_orbit
  simpa only [lower278] using h

theorem space2449_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [404, 84, 36, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(404, 17), (84, 305), (36, 1), (10, 323)]
    (codeMat 179) (codeMat 94) (codeMat 500) false
    det179 det94 inv94
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2449_lower : 16 ≤ frozenWangTable.L0 (spanCodes [404, 84, 36, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2449_orbit
  simpa only [lower338] using h

theorem space2450_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [386, 66, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(386, 264), (66, 280), (38, 69), (22, 68), (10, 259)]
    (codeMat 98) (codeMat 397) (codeMat 250) false
    det98 det397 inv397
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2450_lower : 16 ≤ frozenWangTable.L0 (spanCodes [386, 66, 38, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2450_orbit
  simpa only [lower150] using h

theorem space2451_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [390, 66, 35, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(390, 16), (66, 280), (35, 69), (22, 327), (10, 259)]
    (codeMat 107) (codeMat 415) (codeMat 253) false
    det107 det415 inv415
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2451_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 66, 35, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2451_orbit
  simpa only [lower150] using h

theorem space2452_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [390, 67, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(390, 16), (67, 280), (37, 326), (23, 68), (10, 259)]
    (codeMat 106) (codeMat 425) (codeMat 249) false
    det106 det425 inv425
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2452_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 67, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2452_orbit
  simpa only [lower150] using h

theorem space2453_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [290, 144, 82, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(290, 11), (144, 1), (82, 332), (10, 264), (6, 16)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    det142 det102 inv102
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2453_lower : 16 ≤ frozenWangTable.L0 (spanCodes [290, 144, 82, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 150 space2453_orbit
  simpa only [lower150] using h

theorem space2454_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [387, 67, 33, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(387, 264), (67, 280), (33, 326), (23, 327), (10, 259)]
    (codeMat 99) (codeMat 443) (codeMat 254) false
    det99 det443 inv443
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2454_lower : 16 ≤ frozenWangTable.L0 (spanCodes [387, 67, 33, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space2454_orbit
  simpa only [lower150] using h

theorem space2455_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [304, 131, 82, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(304, 343), (131, 333), (82, 68), (10, 264), (6, 16)]
    (codeMat 207) (codeMat 486) (codeMat 157) false
    det207 det486 inv486
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space2455_lower : 16 ≤ frozenWangTable.L0 (spanCodes [304, 131, 82, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 150 space2455_orbit
  simpa only [lower150] using h

theorem space2456_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [292, 146, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(292, 3), (146, 2), (84, 99), (10, 338)]
    (codeMat 167) (codeMat 125) (codeMat 348) false
    det167 det125 inv125
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2456_lower : 16 ≤ frozenWangTable.L0 (spanCodes [292, 146, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2456_orbit
  simpa only [lower278] using h

theorem space2457_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [310, 128, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(310, 17), (128, 16), (84, 99), (10, 338)]
    (codeMat 167) (codeMat 125) (codeMat 348) false
    det167 det125 inv125
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2457_lower : 16 ≤ frozenWangTable.L0 (spanCodes [310, 128, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2457_orbit
  simpa only [lower338] using h

theorem space2458_orbit :
    frozenWangTable.OrbitImage 275 (spanCodes [384, 84, 54, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 275 [(384, 3), (84, 85), (54, 2), (10, 162)]
    (codeMat 95) (codeMat 499) (codeMat 382) true
    det95 det499 inv499
    (by rw [basis275]; decide +kernel)
    (by rw [basis275]; decide +kernel)

theorem space2458_lower : 16 ≤ frozenWangTable.L0 (spanCodes [384, 84, 54, 10]) := by
  have h := frozenWangTable.lower_le_L0 275 space2458_orbit
  simpa only [lower275] using h

theorem space2459_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [390, 84, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(390, 3), (84, 99), (48, 2), (10, 306)]
    (codeMat 215) (codeMat 501) (codeMat 494) true
    det215 det501 inv501
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space2459_lower : 16 ≤ frozenWangTable.L0 (spanCodes [390, 84, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space2459_orbit
  simpa only [lower278] using h

theorem space2460_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [404, 84, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(404, 338), (84, 114), (34, 322), (10, 323)]
    (codeMat 250) (codeMat 494) (codeMat 501) false
    det250 det494 inv494
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space2460_lower : 16 ≤ frozenWangTable.L0 (spanCodes [404, 84, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space2460_orbit
  simpa only [lower338] using h

theorem space2461_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [277, 151, 84, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(277, 123), (151, 191), (84, 190), (53, 96), (10, 112)]
    (codeMat 93) (codeMat 254) (codeMat 443) false
    det93 det254 inv254
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space2461_lower : 16 ≤ frozenWangTable.L0 (spanCodes [277, 151, 84, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 152 space2461_orbit
  simpa only [lower152] using h

theorem space2462_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 32, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 132), (32, 1), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2462_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 32, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2462_orbit
  simpa only [lower103] using h

theorem space2463_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [81, 33, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(81, 166), (33, 11), (9, 2), (5, 8), (3, 32)]
    (codeMat 267) (codeMat 188) (codeMat 103) false
    det267 det188 inv188
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2463_lower : 15 ≤ frozenWangTable.L0 (spanCodes [81, 33, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2463_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
