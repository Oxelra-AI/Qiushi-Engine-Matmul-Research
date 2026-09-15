import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4480_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 128, 65, 32, 16, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 29), (128, 8), (65, 360), (32, 3), (16, 1), (5, 384), (3, 256)]
    (codeMat 98) (codeMat 103) (codeMat 188) false
    det98 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4480_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 128, 65, 32, 16, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4480_orbit
  simpa only [lower14] using h

theorem space4481_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [264, 129, 64, 33, 17, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(264, 413), (129, 264), (64, 360), (33, 387), (17, 257), (5, 384), (3, 256)]
    (codeMat 107) (codeMat 103) (codeMat 188) false
    det107 det103 inv103
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4481_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 33, 17, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4481_orbit
  simpa only [lower14] using h

theorem space4482_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 64, 35, 19, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 91), (128, 54), (64, 63), (35, 88), (19, 112), (11, 120), (7, 128)]
    (codeMat 86) (codeMat 253) (codeMat 415) false
    det86 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4482_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 35, 19, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4482_orbit
  simpa only [lower11] using h

theorem space4483_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 131, 64, 32, 19, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 8), (131, 240), (64, 40), (32, 1), (19, 198), (11, 197), (7, 128)]
    (codeMat 98) (codeMat 213) (codeMat 470) false
    det98 det213 inv213
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4483_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 32, 19, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4483_orbit
  simpa only [lower11] using h

theorem space4484_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 33, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 139), (130, 9), (67, 119), (33, 480), (16, 8), (11, 392), (7, 360)]
    (codeMat 215) (codeMat 111) (codeMat 412) false
    det215 det111 inv111
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4484_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 33, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4484_orbit
  simpa only [lower14] using h

theorem space4485_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 32, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 406), (131, 284), (67, 227), (32, 384), (16, 256), (10, 224), (7, 8)]
    (codeMat 143) (codeMat 425) (codeMat 249) false
    det143 det425 inv425
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4485_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 32, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4485_orbit
  simpa only [lower14] using h

theorem space4486_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 64, 35, 19, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 100), (128, 63), (64, 9), (35, 160), (19, 120), (9, 8), (7, 128)]
    (codeMat 95) (codeMat 403) (codeMat 403) false
    det95 det403 inv403
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4486_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 35, 19, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4486_orbit
  simpa only [lower11] using h

theorem space4487_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 64, 34, 19, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 32), (129, 120), (64, 8), (34, 196), (19, 71), (9, 1), (7, 128)]
    (codeMat 99) (codeMat 403) (codeMat 403) false
    det99 det403 inv403
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4487_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 34, 19, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4487_orbit
  simpa only [lower11] using h

theorem space4488_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 65, 33, 18, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 327), (130, 2), (65, 1), (33, 440), (18, 16), (9, 8), (7, 256)]
    (codeMat 93) (codeMat 309) (codeMat 309) false
    det93 det309 inv309
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4488_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 33, 18, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 10 space4488_orbit
  simpa only [lower10] using h

theorem space4489_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 64, 34, 19, 8, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 198), (129, 199), (64, 3), (34, 112), (19, 248), (8, 216), (7, 128)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    det92 det443 inv443
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4489_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 34, 19, 8, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4489_orbit
  simpa only [lower11] using h

theorem space4490_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 129, 64, 34, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 373), (129, 227), (64, 511), (34, 258), (18, 256), (10, 259), (6, 130)]
    (codeMat 234) (codeMat 489) (codeMat 241) false
    det234 det489 inv489
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4490_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 34, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space4490_orbit
  simpa only [lower14] using h

theorem space4491_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 16, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 488), (129, 224), (66, 480), (34, 362), (16, 511), (9, 3), (6, 360)]
    (codeMat 355) (codeMat 187) (codeMat 229) false
    det355 det187 inv187
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4491_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 16, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space4491_orbit
  simpa only [lower14] using h

theorem space4492_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 66, 33, 16, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 71), (130, 3), (66, 326), (33, 440), (16, 24), (9, 432), (6, 256)]
    (codeMat 85) (codeMat 382) (codeMat 499) false
    det85 det382 inv382
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4492_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 33, 16, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 10 space4492_orbit
  simpa only [lower10] using h

theorem space4493_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 65, 35, 16, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 105), (128, 8), (65, 511), (35, 387), (16, 1), (11, 385), (5, 130)]
    (codeMat 226) (codeMat 335) (codeMat 426) false
    det226 det335 inv335
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4493_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 65, 35, 16, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4493_orbit
  simpa only [lower14] using h

theorem space4494_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 128, 65, 35, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 374), (128, 9), (65, 256), (35, 373), (16, 8), (10, 105), (5, 511)]
    (codeMat 342) (codeMat 102) (codeMat 156) false
    det342 det102 inv102
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4494_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 35, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4494_orbit
  simpa only [lower14] using h

theorem space4495_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 130, 66, 33, 19, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 2), (130, 325), (66, 326), (33, 272), (19, 424), (8, 432), (5, 256)]
    (codeMat 92) (codeMat 234) (codeMat 461) false
    det92 det234 inv234
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4495_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 33, 19, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space4495_orbit
  simpa only [lower10] using h

theorem space4496_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 67, 33, 18, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 258), (130, 1), (67, 70), (33, 272), (18, 8), (8, 432), (5, 256)]
    (codeMat 93) (codeMat 106) (codeMat 396) false
    det93 det106 inv106
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4496_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 18, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space4496_orbit
  simpa only [lower10] using h

theorem space4497_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 64, 33, 17, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 326), (130, 325), (64, 2), (33, 176), (17, 168), (8, 16), (5, 256)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    det84 det426 inv426
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4497_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 33, 17, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space4497_orbit
  simpa only [lower10] using h

theorem space4498_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 64, 32, 17, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 232), (131, 488), (64, 128), (32, 3), (17, 23), (8, 2), (5, 8)]
    (codeMat 266) (codeMat 190) (codeMat 355) false
    det266 det190 inv190
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4498_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 17, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4498_orbit
  simpa only [lower14] using h

theorem space4499_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [259, 130, 65, 33, 16, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(259, 326), (130, 1), (65, 2), (33, 176), (16, 8), (8, 16), (5, 256)]
    (codeMat 85) (codeMat 298) (codeMat 270) false
    det85 det298 inv298
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4499_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 33, 16, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space4499_orbit
  simpa only [lower10] using h

theorem space4500_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 67, 32, 19, 11, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 80), (131, 112), (67, 120), (32, 2), (19, 70), (11, 71), (4, 128)]
    (codeMat 98) (codeMat 249) (codeMat 425) false
    det98 det249 inv249
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4500_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 19, 11, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space4500_orbit
  simpa only [lower11] using h

theorem space4501_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 65, 33, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (130, 384), (65, 256), (33, 105), (17, 406), (10, 276), (4, 8)]
    (codeMat 334) (codeMat 212) (codeMat 86) false
    det334 det212 inv212
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4501_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 33, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4501_orbit
  simpa only [lower14] using h

theorem space4502_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 64, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 96), (131, 232), (64, 360), (32, 1), (16, 3), (10, 29), (4, 8)]
    (codeMat 330) (codeMat 87) (codeMat 468) false
    det330 det87 inv87
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4502_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4502_orbit
  simpa only [lower14] using h

theorem space4503_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 18, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 105), (129, 276), (66, 406), (34, 104), (18, 256), (9, 384), (4, 8)]
    (codeMat 206) (codeMat 204) (codeMat 114) false
    det206 det204 inv204
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4503_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 18, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4503_orbit
  simpa only [lower14] using h

theorem space4504_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 67, 35, 19, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 210), (128, 54), (67, 237), (35, 208), (19, 240), (8, 40), (4, 128)]
    (codeMat 86) (codeMat 241) (codeMat 489) false
    det86 det241 inv241
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4504_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 67, 35, 19, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space4504_orbit
  simpa only [lower11] using h

theorem space4505_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 69, 37, 17, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 20), (133, 23), (69, 22), (37, 276), (17, 503), (13, 406), (3, 8)]
    (codeMat 396) (codeMat 474) (codeMat 395) false
    det396 det474 inv474
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4505_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 37, 17, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4505_orbit
  simpa only [lower14] using h

theorem space4506_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 68, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 384), (129, 488), (68, 392), (33, 510), (16, 2), (9, 511), (3, 360)]
    (codeMat 354) (codeMat 377) (codeMat 369) false
    det354 det377 inv377
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4506_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4506_orbit
  simpa only [lower14] using h

theorem space4507_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [265, 136, 73, 40, 25, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(265, 180), (136, 71), (73, 54), (40, 128), (25, 112), (4, 32), (3, 8)]
    (codeMat 142) (codeMat 474) (codeMat 395) false
    det142 det474 inv474
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4507_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 136, 73, 40, 25, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4507_orbit
  simpa only [lower11] using h

theorem space4508_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [265, 128, 65, 32, 17, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(265, 21), (128, 8), (65, 360), (32, 130), (17, 257), (4, 128), (3, 256)]
    (codeMat 99) (codeMat 99) (codeMat 172) false
    det99 det99 inv99
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4508_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 128, 65, 32, 17, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4508_orbit
  simpa only [lower14] using h

theorem space4509_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 64, 32, 20, 13, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 1), (129, 149), (64, 511), (32, 8), (20, 96), (13, 392), (2, 360)]
    (codeMat 213) (codeMat 207) (codeMat 370) false
    det213 det207 inv207
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4509_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 64, 32, 20, 13, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4509_orbit
  simpa only [lower14] using h

theorem space4510_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 68, 32, 16, 12, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 227), (129, 97), (68, 284), (32, 3), (16, 1), (12, 28), (2, 8)]
    (codeMat 394) (codeMat 102) (codeMat 156) false
    det394 det102 inv102
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4510_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 68, 32, 16, 12, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4510_orbit
  simpa only [lower14] using h

theorem space4511_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 36, 21, 9, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 406), (133, 105), (65, 130), (36, 384), (21, 104), (9, 128), (2, 8)]
    (codeMat 206) (codeMat 298) (codeMat 270) false
    det206 det298 inv298
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4511_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 36, 21, 9, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4511_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
