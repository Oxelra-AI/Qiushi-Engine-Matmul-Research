import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4448_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 131, 67, 32, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 23), (131, 22), (67, 20), (32, 511), (17, 406), (10, 276), (6, 8)]
    (codeMat 460) (codeMat 500) (codeMat 94) false
    det460 det500 inv500
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4448_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space4448_orbit
  simpa only [lower14] using h

theorem space4449_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 65, 35, 19, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (128, 32), (65, 216), (35, 70), (19, 196), (9, 3), (6, 128)]
    (codeMat 99) (codeMat 425) (codeMat 249) false
    det99 det425 inv425
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4449_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 19, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space4449_orbit
  simpa only [lower11] using h

theorem space4450_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 65, 33, 18, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (130, 8), (65, 40), (33, 198), (18, 1), (11, 69), (7, 128)]
    (codeMat 107) (codeMat 355) (codeMat 190) false
    det107 det355 inv355
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4450_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 33, 18, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space4450_orbit
  simpa only [lower11] using h

theorem space4451_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 32, 16, 11, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 404), (131, 126), (67, 119), (32, 256), (16, 384), (11, 392), (7, 360)]
    (codeMat 159) (codeMat 473) (codeMat 409) false
    det159 det473 inv473
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4451_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 32, 16, 11, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4451_orbit
  simpa only [lower14] using h

theorem space4452_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 32, 18, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 29), (131, 22), (65, 2), (32, 360), (18, 384), (9, 128), (7, 8)]
    (codeMat 205) (codeMat 412) (codeMat 111) false
    det205 det412 inv412
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4452_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 32, 18, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space4452_orbit
  simpa only [lower14] using h

theorem space4453_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 66, 32, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 276), (131, 373), (66, 235), (32, 2), (18, 384), (10, 387), (4, 130)]
    (codeMat 234) (codeMat 241) (codeMat 489) false
    det234 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4453_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 66, 32, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4453_orbit
  simpa only [lower14] using h

theorem space4454_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (131, 480), (65, 256), (32, 9), (17, 31), (10, 28), (4, 8)]
    (codeMat 331) (codeMat 214) (codeMat 214) false
    det331 det214 inv214
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4454_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4454_orbit
  simpa only [lower14] using h

theorem space4455_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 64, 35, 16, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 68), (128, 3), (64, 1), (35, 160), (16, 24), (8, 8), (4, 256)]
    (codeMat 84) (codeMat 275) (codeMat 275) false
    det84 det275 inv275
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4455_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 35, 16, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space4455_orbit
  simpa only [lower10] using h

theorem space4456_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 64, 33, 16, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 284), (130, 8), (64, 130), (33, 149), (16, 1), (8, 2), (4, 511)]
    (codeMat 426) (codeMat 302) (codeMat 302) false
    det426 det302 inv302
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4456_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 33, 16, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4456_orbit
  simpa only [lower14] using h

theorem space4457_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 65, 33, 17, 8, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 264), (130, 256), (65, 128), (33, 149), (17, 148), (8, 2), (4, 360)]
    (codeMat 354) (codeMat 396) (codeMat 106) false
    det354 det396 inv396
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4457_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 33, 17, 8, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4457_orbit
  simpa only [lower14] using h

theorem space4458_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 65, 33, 17, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 509), (130, 3), (65, 1), (33, 264), (17, 136), (9, 8), (4, 360)]
    (codeMat 157) (codeMat 279) (codeMat 279) false
    det157 det279 inv279
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4458_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 33, 17, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space4458_orbit
  simpa only [lower14] using h

theorem space4459_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 64, 34, 17, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 406), (129, 284), (64, 511), (34, 22), (17, 28), (10, 31), (5, 8)]
    (codeMat 395) (codeMat 489) (codeMat 241) false
    det395 det489 inv489
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4459_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 64, 34, 17, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4459_orbit
  simpa only [lower14] using h

theorem space4460_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 67, 35, 18, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 160), (128, 216), (67, 240), (35, 68), (18, 3), (11, 198), (5, 128)]
    (codeMat 107) (codeMat 346) (codeMat 459) false
    det107 det346 inv346
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4460_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 67, 35, 18, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space4460_orbit
  simpa only [lower11] using h

theorem space4461_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 130, 67, 33, 18, 11, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 196), (130, 1), (67, 70), (33, 160), (18, 8), (11, 112), (5, 128)]
    (codeMat 93) (codeMat 330) (codeMat 394) false
    det93 det330 inv330
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4461_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 67, 33, 18, 11, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space4461_orbit
  simpa only [lower11] using h

theorem space4462_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 34, 19, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 30), (129, 21), (66, 23), (34, 414), (19, 381), (8, 511), (5, 8)]
    (codeMat 397) (codeMat 491) (codeMat 375) false
    det397 det491 inv491
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4462_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 34, 19, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space4462_orbit
  simpa only [lower14] using h

theorem space4463_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 65, 33, 16, 8, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 326), (130, 3), (65, 2), (33, 176), (16, 24), (8, 16), (5, 256)]
    (codeMat 85) (codeMat 314) (codeMat 271) false
    det85 det314 inv314
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4463_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 33, 16, 8, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space4463_orbit
  simpa only [lower10] using h

theorem space4464_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 129, 64, 32, 20, 12, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 2), (129, 68), (64, 325), (32, 16), (20, 160), (12, 168), (2, 256)]
    (codeMat 85) (codeMat 225) (codeMat 169) false
    det85 det225 inv225
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4464_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 64, 32, 20, 12, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4464_orbit
  simpa only [lower10] using h

theorem space4465_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 133, 65, 36, 21, 12, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 228), (133, 82), (65, 63), (36, 32), (21, 80), (12, 248), (2, 128)]
    (codeMat 94) (codeMat 345) (codeMat 345) false
    det94 det345 inv345
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4465_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 36, 21, 12, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4465_orbit
  simpa only [lower11] using h

theorem space4466_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [261, 129, 64, 32, 20, 13, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(261, 326), (129, 68), (64, 325), (32, 432), (20, 160), (13, 424), (2, 256)]
    (codeMat 93) (codeMat 481) (codeMat 185) false
    det93 det481 inv481
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4466_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 129, 64, 32, 20, 13, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4466_orbit
  simpa only [lower10] using h

theorem space4467_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [264, 129, 64, 32, 16, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(264, 68), (129, 160), (64, 256), (32, 1), (16, 2), (4, 8), (2, 16)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    det266 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4467_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 32, 16, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4467_orbit
  simpa only [lower10] using h

theorem space4468_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [265, 136, 72, 41, 25, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(265, 78), (136, 228), (72, 63), (41, 120), (25, 248), (5, 8), (2, 32)]
    (codeMat 143) (codeMat 489) (codeMat 241) false
    det143 det489 inv489
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4468_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 136, 72, 41, 25, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space4468_orbit
  simpa only [lower11] using h

theorem space4469_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [264, 129, 64, 32, 17, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(264, 68), (129, 170), (64, 325), (32, 256), (17, 168), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    det142 det337 inv337
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4469_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 129, 64, 32, 17, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space4469_orbit
  simpa only [lower10] using h

theorem space4470_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [265, 128, 64, 33, 17, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(265, 118), (128, 128), (64, 384), (33, 510), (17, 150), (5, 1), (2, 2)]
    (codeMat 305) (codeMat 380) (codeMat 117) false
    det305 det380 inv380
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4470_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 128, 64, 33, 17, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4470_orbit
  simpa only [lower14] using h

theorem space4471_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [288, 161, 64, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(288, 3), (161, 124), (64, 9), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 86) (codeMat 165) (codeMat 163) false
    det86 det165 inv165
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4471_lower : 12 ≤ frozenWangTable.L0 (spanCodes [288, 161, 64, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space4471_orbit
  simpa only [lower14] using h

theorem space4472_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 128, 68, 32, 16, 13, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 1), (128, 3), (68, 71), (32, 8), (16, 24), (13, 440), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    det84 det95 inv95
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4472_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 32, 16, 13, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4472_orbit
  simpa only [lower10] using h

theorem space4473_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 64, 32, 20, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 20), (128, 3), (64, 2), (32, 256), (20, 224), (8, 128), (3, 8)]
    (codeMat 140) (codeMat 282) (codeMat 267) false
    det140 det282 inv282
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4473_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 64, 32, 20, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4473_orbit
  simpa only [lower14] using h

theorem space4474_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 68, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (132, 21), (68, 20), (36, 128), (16, 360), (9, 256), (3, 8)]
    (codeMat 204) (codeMat 226) (codeMat 141) false
    det204 det226 inv226
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4474_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4474_orbit
  simpa only [lower14] using h

theorem space4475_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 68, 32, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 8), (128, 128), (68, 392), (32, 1), (16, 2), (9, 511), (3, 360)]
    (codeMat 298) (codeMat 93) (codeMat 372) false
    det298 det93 inv93
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4475_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 32, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4475_orbit
  simpa only [lower14] using h

theorem space4476_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 72, 32, 24, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 168), (128, 256), (72, 325), (32, 2), (24, 1), (4, 16), (3, 8)]
    (codeMat 266) (codeMat 225) (codeMat 169) false
    det266 det225 inv225
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space4476_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 72, 32, 24, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space4476_orbit
  simpa only [lower10] using h

theorem space4477_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [289, 160, 64, 16, 8, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(289, 118), (160, 30), (64, 8), (16, 3), (8, 1), (4, 384), (3, 128)]
    (codeMat 98) (codeMat 307) (codeMat 311) false
    det98 det307 inv307
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space4477_lower : 12 ≤ frozenWangTable.L0 (spanCodes [289, 160, 64, 16, 8, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space4477_orbit
  simpa only [lower14] using h

theorem space4478_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [265, 136, 72, 40, 25, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(265, 180), (136, 248), (72, 32), (40, 128), (25, 196), (5, 2), (3, 3)]
    (codeMat 177) (codeMat 498) (codeMat 206) false
    det177 det498 inv498
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4478_lower : 12 ≤ frozenWangTable.L0 (spanCodes [265, 136, 72, 40, 25, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4478_orbit
  simpa only [lower11] using h

theorem space4479_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [264, 137, 72, 41, 25, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(264, 240), (137, 101), (72, 40), (41, 197), (25, 69), (5, 3), (3, 1)]
    (codeMat 177) (codeMat 481) (codeMat 185) false
    det177 det481 inv481
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space4479_lower : 12 ≤ frozenWangTable.L0 (spanCodes [264, 137, 72, 41, 25, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space4479_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
