import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3808_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 128, 65, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 324), (128, 3), (65, 325), (35, 160), (18, 24), (10, 424), (4, 256)]
    (codeMat 92) (codeMat 339) (codeMat 467) false
    det92 det339 inv339
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3808_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space3808_orbit
  simpa only [lower10] using h

theorem space3809_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 66, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 259), (129, 70), (66, 71), (32, 24), (18, 432), (10, 440), (5, 256)]
    (codeMat 85) (codeMat 253) (codeMat 415) false
    det85 det253 inv253
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3809_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space3809_orbit
  simpa only [lower10] using h

theorem space3810_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 130, 64, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 257), (130, 3), (64, 325), (33, 264), (18, 24), (10, 424), (5, 256)]
    (codeMat 93) (codeMat 87) (codeMat 468) false
    det93 det87 inv87
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3810_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space3810_orbit
  simpa only [lower10] using h

theorem space3811_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 65, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 10), (131, 30), (65, 3), (33, 136), (18, 384), (10, 232), (5, 8)]
    (codeMat 205) (codeMat 185) (codeMat 481) false
    det205 det185 inv185
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3811_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3811_orbit
  simpa only [lower14] using h

theorem space3812_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 66, 34, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 381), (131, 414), (66, 235), (34, 259), (18, 3), (10, 387), (5, 130)]
    (codeMat 163) (codeMat 375) (codeMat 491) false
    det163 det375 inv375
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3812_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 66, 34, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3812_orbit
  simpa only [lower14] using h

theorem space3813_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 66, 35, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 258), (130, 256), (66, 257), (35, 503), (17, 97), (10, 105), (6, 130)]
    (codeMat 348) (codeMat 481) (codeMat 185) false
    det348 det481 inv481
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3813_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 35, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3813_orbit
  simpa only [lower14] using h

theorem space3814_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 65, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 363), (130, 1), (65, 3), (35, 276), (18, 8), (10, 138), (6, 511)]
    (codeMat 477) (codeMat 299) (codeMat 318) false
    det477 det299 inv299
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3814_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3814_orbit
  simpa only [lower14] using h

theorem space3815_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 65, 34, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 160), (128, 216), (65, 40), (34, 196), (16, 3), (10, 197), (7, 128)]
    (codeMat 106) (codeMat 339) (codeMat 467) false
    det106 det339 inv339
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3815_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 34, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space3815_orbit
  simpa only [lower11] using h

theorem space3816_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 67, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 138), (129, 373), (67, 235), (32, 128), (18, 360), (10, 232), (5, 8)]
    (codeMat 143) (codeMat 171) (codeMat 485) false
    det143 det171 inv171
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3816_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3816_orbit
  simpa only [lower14] using h

theorem space3817_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 131, 67, 34, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 381), (131, 97), (67, 105), (34, 259), (18, 256), (10, 257), (5, 130)]
    (codeMat 226) (codeMat 485) (codeMat 171) false
    det226 det485 inv485
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3817_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 67, 34, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3817_orbit
  simpa only [lower14] using h

theorem space3818_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 128, 66, 34, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 96), (128, 256), (66, 224), (34, 97), (17, 284), (10, 227), (4, 8)]
    (codeMat 270) (codeMat 141) (codeMat 226) false
    det270 det141 inv141
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3818_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3818_orbit
  simpa only [lower14] using h

theorem space3819_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 509), (128, 1), (65, 511), (34, 264), (18, 8), (10, 392), (4, 360)]
    (codeMat 156) (codeMat 335) (codeMat 426) false
    det156 det335 inv335
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3819_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3819_orbit
  simpa only [lower14] using h

theorem space3820_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 65, 35, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 508), (130, 2), (65, 3), (35, 104), (18, 128), (10, 136), (7, 360)]
    (codeMat 213) (codeMat 281) (codeMat 281) false
    det213 det281 inv281
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3820_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 65, 35, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3820_orbit
  simpa only [lower14] using h

theorem space3821_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 64, 32, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 131), (130, 3), (64, 256), (32, 8), (17, 284), (10, 227), (6, 130)]
    (codeMat 277) (codeMat 86) (codeMat 212) false
    det277 det86 inv86
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3821_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 32, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3821_orbit
  simpa only [lower14] using h

theorem space3822_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 66, 36, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 9), (132, 353), (66, 404), (36, 8), (22, 97), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 140) (codeMat 98) false
    det478 det140 inv140
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3822_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 66, 36, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3822_orbit
  simpa only [lower14] using h

theorem space3823_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [274, 128, 66, 50, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(274, 427), (128, 325), (66, 170), (50, 424), (10, 168), (4, 24), (1, 16)]
    (codeMat 142) (codeMat 174) (codeMat 359) false
    det142 det174 inv174
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3823_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 128, 66, 50, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3823_orbit
  simpa only [lower10] using h

theorem space3824_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 232), (128, 128), (65, 360), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 271) (codeMat 117) (codeMat 380) false
    det271 det117 inv117
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3824_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3824_orbit
  simpa only [lower14] using h

theorem space3825_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 130, 67, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 70), (130, 3), (67, 199), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 85) (codeMat 379) (codeMat 247) false
    det85 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3825_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space3825_orbit
  simpa only [lower11] using h

theorem space3826_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 67, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 278), (130, 9), (67, 119), (33, 276), (18, 8), (10, 503), (4, 130)]
    (codeMat 478) (codeMat 106) (codeMat 396) false
    det478 det106 inv106
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3826_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 67, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3826_orbit
  simpa only [lower14] using h

theorem space3827_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 128, 65, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 104), (128, 128), (65, 360), (33, 97), (18, 130), (10, 381), (4, 8)]
    (codeMat 271) (codeMat 85) (codeMat 340) false
    det271 det85 inv85
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3827_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3827_orbit
  simpa only [lower14] using h

theorem space3828_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 97), (133, 227), (65, 8), (36, 360), (20, 362), (8, 1), (2, 511)]
    (codeMat 426) (codeMat 407) (codeMat 405) false
    det426 det407 inv407
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3828_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3828_orbit
  simpa only [lower14] using h

theorem space3829_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 128, 69, 37, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 21), (128, 1), (69, 23), (37, 381), (20, 97), (8, 511), (2, 8)]
    (codeMat 460) (codeMat 335) (codeMat 426) false
    det460 det335 inv335
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3829_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 37, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3829_orbit
  simpa only [lower14] using h

theorem space3830_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 132, 64, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 325), (132, 324), (64, 3), (37, 424), (21, 416), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 397) (codeMat 250) false
    det84 det397 inv397
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3830_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space3830_orbit
  simpa only [lower10] using h

theorem space3831_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 69, 32, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 2), (132, 509), (69, 150), (32, 128), (21, 96), (8, 384), (2, 360)]
    (codeMat 157) (codeMat 234) (codeMat 461) false
    det157 det234 inv234
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3831_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 32, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3831_orbit
  simpa only [lower14] using h

theorem space3832_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 145, 80, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 254), (145, 246), (80, 30), (48, 1), (8, 3), (5, 256), (2, 384)]
    (codeMat 98) (codeMat 445) (codeMat 478) false
    det98 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3832_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 80, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3832_orbit
  simpa only [lower14] using h

theorem space3833_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 36, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 276), (133, 235), (65, 130), (36, 256), (21, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 282) (codeMat 267) false
    det206 det282 inv282
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3833_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 36, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3833_orbit
  simpa only [lower14] using h

theorem space3834_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 64, 37, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 112), (129, 88), (64, 8), (37, 70), (17, 131), (9, 1), (3, 128)]
    (codeMat 99) (codeMat 307) (codeMat 311) false
    det99 det307 inv307
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3834_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 37, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3834_orbit
  simpa only [lower11] using h

theorem space3835_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 128, 65, 37, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (128, 8), (65, 216), (37, 198), (17, 129), (9, 3), (3, 128)]
    (codeMat 99) (codeMat 299) (codeMat 318) false
    det99 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3835_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 37, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3835_orbit
  simpa only [lower11] using h

theorem space3836_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 144, 81, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 10), (144, 3), (81, 373), (48, 8), (9, 360), (4, 128), (3, 384)]
    (codeMat 86) (codeMat 115) (codeMat 492) false
    det86 det115 inv115
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3836_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 81, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3836_orbit
  simpa only [lower14] using h

theorem space3837_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 145, 65, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 252), (145, 127), (65, 1), (33, 352), (9, 8), (4, 256), (3, 384)]
    (codeMat 93) (codeMat 403) (codeMat 403) false
    det93 det403 inv403
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3837_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 145, 65, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3837_orbit
  simpa only [lower14] using h

theorem space3838_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 193, 33, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 199), (193, 71), (33, 31), (17, 55), (9, 63), (4, 3), (3, 1)]
    (codeMat 273) (codeMat 253) (codeMat 415) false
    det273 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3838_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 193, 33, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3838_orbit
  simpa only [lower11] using h

theorem space3839_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 129, 64, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 483), (129, 127), (64, 9), (49, 352), (9, 8), (5, 128), (3, 384)]
    (codeMat 95) (codeMat 183) (codeMat 419) false
    det95 det183 inv183
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3839_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 129, 64, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3839_orbit
  simpa only [lower14] using h


end QiushiMatmul.FrozenWang
