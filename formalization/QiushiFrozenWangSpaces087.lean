import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2784_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 130, 68, 32, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 1), (130, 2), (68, 324), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    det85 det84 inv84
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2784_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 130, 68, 32, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2784_orbit
  simpa only [lower10] using h

theorem space2785_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 160, 64, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 257), (160, 97), (64, 130), (18, 360), (10, 151), (6, 1), (1, 2)]
    (codeMat 369) (codeMat 394) (codeMat 330) false
    det369 det394 inv394
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2785_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 160, 64, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2785_orbit
  simpa only [lower14] using h

theorem space2786_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 162, 66, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    det142 det428 inv428
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2786_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 162, 66, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2786_orbit
  simpa only [lower10] using h

theorem space2787_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [256, 160, 66, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(256, 325), (160, 68), (66, 162), (16, 256), (10, 160), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 396) (codeMat 106) false
    det142 det396 inv396
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space2787_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 66, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space2787_orbit
  simpa only [lower10] using h

theorem space2788_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 8), (160, 97), (66, 21), (18, 360), (10, 151), (4, 1), (1, 2)]
    (codeMat 481) (codeMat 142) (codeMat 354) false
    det481 det142 inv142
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space2788_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space2788_orbit
  simpa only [lower14] using h

theorem space2789_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [290, 130, 66, 18, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(290, 28), (130, 219), (66, 89), (18, 216), (10, 88), (4, 32), (1, 8)]
    (codeMat 142) (codeMat 275) (codeMat 275) false
    det142 det275 inv275
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space2789_lower : 12 ≤ frozenWangTable.L0 (spanCodes [290, 130, 66, 18, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space2789_orbit
  simpa only [lower11] using h

theorem space2790_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 70), (128, 1), (64, 2), (34, 112), (16, 8), (10, 80), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 298) (codeMat 270) false
    det84 det298 inv298
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2790_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2790_orbit
  simpa only [lower3] using h

theorem space2791_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 69), (128, 1), (66, 70), (32, 40), (16, 8), (10, 112), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    det84 det334 inv334
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2791_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2791_orbit
  simpa only [lower3] using h

theorem space2792_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    det84 det110 inv110
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2792_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2792_orbit
  simpa only [lower3] using h

theorem space2793_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 33, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 454), (128, 3), (65, 455), (33, 496), (17, 472), (9, 504), (4, 384), (3, 256)]
    (codeMat 84) (codeMat 379) (codeMat 247) false
    det84 det379 inv379
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2793_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2793_orbit
  simpa only [lower3] using h

theorem space2794_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [96, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(96, 96), (21, 20), (10, 10)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    det401 det277 inv277
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2794_lower : 18 ≤ frozenWangTable.L0 (spanCodes [96, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2794_orbit
  simpa only [lower454] using h

theorem space2795_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [96, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(96, 126), (22, 30), (10, 10)]
    (codeMat 473) (codeMat 307) (codeMat 311) false
    det473 det307 inv307
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2795_lower : 18 ≤ frozenWangTable.L0 (spanCodes [96, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2795_orbit
  simpa only [lower454] using h

theorem space2796_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [96, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(96, 126), (23, 30), (10, 10)]
    (codeMat 345) (codeMat 311) (codeMat 307) false
    det345 det311 inv311
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2796_lower : 18 ≤ frozenWangTable.L0 (spanCodes [96, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2796_orbit
  simpa only [lower454] using h

theorem space2797_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [69, 37, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(69, 129), (37, 10), (10, 20)]
    (codeMat 345) (codeMat 156) (codeMat 102) false
    det345 det156 inv156
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2797_lower : 18 ≤ frozenWangTable.L0 (spanCodes [69, 37, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2797_orbit
  simpa only [lower455] using h

theorem space2798_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [70, 38, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(70, 149), (38, 30), (10, 20)]
    (codeMat 473) (codeMat 188) (codeMat 103) false
    det473 det188 inv188
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2798_lower : 18 ≤ frozenWangTable.L0 (spanCodes [70, 38, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2798_orbit
  simpa only [lower455] using h

theorem space2799_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [81, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(81, 129), (49, 20), (10, 10)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    det330 det270 inv270
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2799_lower : 18 ≤ frozenWangTable.L0 (spanCodes [81, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2799_orbit
  simpa only [lower455] using h

theorem space2800_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [83, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(83, 139), (51, 30), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    det458 det302 inv302
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2800_lower : 18 ≤ frozenWangTable.L0 (spanCodes [83, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2800_orbit
  simpa only [lower455] using h

theorem space2801_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [87, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(87, 171), (55, 20), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    det267 det318 inv318
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2801_lower : 18 ≤ frozenWangTable.L0 (spanCodes [87, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2801_orbit
  simpa only [lower456] using h

theorem space2802_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [129, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(129, 20), (96, 96), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    det266 det266 inv266
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2802_lower : 18 ≤ frozenWangTable.L0 (spanCodes [129, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2802_orbit
  simpa only [lower454] using h

theorem space2803_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [131, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(131, 30), (96, 126), (10, 10)]
    (codeMat 474) (codeMat 299) (codeMat 318) true
    det474 det299 inv299
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2803_lower : 18 ≤ frozenWangTable.L0 (spanCodes [131, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2803_orbit
  simpa only [lower454] using h

theorem space2804_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [132, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(132, 168), (96, 162), (10, 68)]
    (codeMat 99) (codeMat 226) (codeMat 141) false
    det99 det226 inv226
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2804_lower : 18 ≤ frozenWangTable.L0 (spanCodes [132, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2804_orbit
  simpa only [lower461] using h

theorem space2805_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [133, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(133, 240), (96, 164), (10, 10)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    det267 det282 inv282
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2805_lower : 18 ≤ frozenWangTable.L0 (spanCodes [133, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2805_orbit
  simpa only [lower468] using h

theorem space2806_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [134, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(134, 164), (96, 240), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    det275 det313 inv313
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2806_lower : 18 ≤ frozenWangTable.L0 (spanCodes [134, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2806_orbit
  simpa only [lower468] using h

theorem space2807_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [135, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(135, 240), (96, 180), (10, 10)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    det331 det282 inv282
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2807_lower : 18 ≤ frozenWangTable.L0 (spanCodes [135, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2807_orbit
  simpa only [lower464] using h

theorem space2808_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [145, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(145, 20), (96, 96), (10, 10)]
    (codeMat 394) (codeMat 298) (codeMat 270) true
    det394 det298 inv298
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2808_lower : 18 ≤ frozenWangTable.L0 (spanCodes [145, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2808_orbit
  simpa only [lower454] using h

theorem space2809_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [147, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(147, 30), (96, 126), (10, 10)]
    (codeMat 346) (codeMat 271) (codeMat 314) true
    det346 det271 inv271
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2809_lower : 18 ≤ frozenWangTable.L0 (spanCodes [147, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2809_orbit
  simpa only [lower454] using h

theorem space2810_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [148, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(148, 240), (96, 164), (10, 10)]
    (codeMat 395) (codeMat 314) (codeMat 271) false
    det395 det314 inv314
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2810_lower : 18 ≤ frozenWangTable.L0 (spanCodes [148, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2810_orbit
  simpa only [lower468] using h

theorem space2811_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [149, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(149, 168), (96, 162), (10, 68)]
    (codeMat 115) (codeMat 482) (codeMat 143) false
    det115 det482 inv482
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2811_lower : 18 ≤ frozenWangTable.L0 (spanCodes [149, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2811_orbit
  simpa only [lower461] using h

theorem space2812_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [150, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(150, 180), (96, 240), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    det275 det313 inv313
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2812_lower : 18 ≤ frozenWangTable.L0 (spanCodes [150, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2812_orbit
  simpa only [lower464] using h

theorem space2813_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [151, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(151, 164), (96, 240), (10, 10)]
    (codeMat 403) (codeMat 285) (codeMat 317) false
    det403 det285 inv285
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2813_lower : 18 ≤ frozenWangTable.L0 (spanCodes [151, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2813_orbit
  simpa only [lower468] using h

theorem space2814_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [161, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(161, 161), (96, 191), (10, 20)]
    (codeMat 215) (codeMat 303) (codeMat 286) true
    det215 det303 inv303
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2814_lower : 18 ≤ frozenWangTable.L0 (spanCodes [161, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2814_orbit
  simpa only [lower456] using h

theorem space2815_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [162, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(162, 149), (96, 30), (10, 129)]
    (codeMat 242) (codeMat 285) (codeMat 317) false
    det242 det285 inv285
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2815_lower : 18 ≤ frozenWangTable.L0 (spanCodes [162, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2815_orbit
  simpa only [lower455] using h


end QiushiMatmul.FrozenWang
