import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3776_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [274, 144, 64, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(274, 101), (144, 40), (64, 216), (50, 69), (10, 197), (6, 1), (1, 3)]
    (codeMat 177) (codeMat 395) (codeMat 474) false
    det177 det395 inv395
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3776_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 144, 64, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3776_orbit
  simpa only [lower11] using h

theorem space3777_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [274, 146, 66, 50, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(274, 231), (146, 63), (66, 79), (50, 199), (10, 71), (6, 3), (1, 1)]
    (codeMat 177) (codeMat 403) (codeMat 403) false
    det177 det403 inv403
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3777_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 146, 66, 50, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3777_orbit
  simpa only [lower11] using h

theorem space3778_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [275, 144, 67, 50, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(275, 93), (144, 256), (67, 347), (50, 336), (10, 338), (7, 5)]
    (codeMat 407) (codeMat 425) (codeMat 249) true
    det407 det425 inv425
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3778_lower : 12 ≤ frozenWangTable.L0 (spanCodes [275, 144, 67, 50, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 25 space3778_orbit
  simpa only [lower25] using h

theorem space3779_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [275, 146, 65, 50, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(275, 266), (146, 8), (65, 260), (50, 336), (10, 341), (7, 2)]
    (codeMat 335) (codeMat 369) (codeMat 377) true
    det335 det369 inv369
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3779_lower : 12 ≤ frozenWangTable.L0 (spanCodes [275, 146, 65, 50, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 25 space3779_orbit
  simpa only [lower25] using h

theorem space3780_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [273, 144, 80, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(273, 486), (144, 1), (80, 324), (33, 416), (8, 256), (5, 16), (2, 8)]
    (codeMat 142) (codeMat 354) (codeMat 142) false
    det142 det354 inv354
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3780_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 144, 80, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 10 space3780_orbit
  simpa only [lower10] using h

theorem space3781_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [273, 145, 65, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(273, 230), (145, 61), (65, 130), (49, 208), (8, 128), (5, 32), (2, 40)]
    (codeMat 143) (codeMat 426) (codeMat 335) false
    det143 det426 inv426
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3781_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 145, 65, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3781_orbit
  simpa only [lower11] using h

theorem space3782_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 128, 81, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 257), (128, 325), (81, 246), (48, 256), (9, 432), (4, 8), (3, 24)]
    (codeMat 142) (codeMat 206) (codeMat 498) false
    det142 det206 inv206
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3782_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 128, 81, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3782_orbit
  simpa only [lower10] using h

theorem space3783_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 144, 80, 32, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 324), (144, 325), (80, 326), (32, 256), (9, 432), (5, 16), (3, 24)]
    (codeMat 140) (codeMat 458) (codeMat 458) false
    det140 det458 inv458
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3783_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 80, 32, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3783_orbit
  simpa only [lower10] using h

theorem space3784_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 129, 81, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 381), (129, 232), (81, 413), (48, 130), (9, 3), (5, 256), (3, 384)]
    (codeMat 99) (codeMat 431) (codeMat 477) false
    det99 det431 inv431
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3784_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 129, 81, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3784_orbit
  simpa only [lower14] using h

theorem space3785_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [272, 145, 65, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(272, 70), (145, 31), (65, 219), (49, 88), (9, 216), (5, 40), (3, 32)]
    (codeMat 142) (codeMat 443) (codeMat 254) false
    det142 det443 inv443
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3785_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 145, 65, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3785_orbit
  simpa only [lower11] using h

theorem space3786_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [272, 128, 80, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(272, 352), (128, 256), (80, 224), (48, 360), (9, 511), (4, 1), (3, 3)]
    (codeMat 305) (codeMat 205) (codeMat 242) false
    det305 det205 inv205
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3786_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 128, 80, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3786_orbit
  simpa only [lower14] using h

theorem space3787_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [273, 129, 81, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(273, 98), (129, 246), (81, 413), (49, 96), (8, 360), (4, 128), (2, 384)]
    (codeMat 94) (codeMat 241) (codeMat 489) false
    det94 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3787_lower : 12 ≤ frozenWangTable.L0 (spanCodes [273, 129, 81, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3787_orbit
  simpa only [lower14] using h

theorem space3788_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [274, 144, 66, 48, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(274, 148), (144, 54), (66, 121), (48, 128), (10, 112), (4, 32), (1, 8)]
    (codeMat 143) (codeMat 401) (codeMat 401) false
    det143 det401 inv401
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3788_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 144, 66, 48, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3788_orbit
  simpa only [lower11] using h

theorem space3789_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [262, 134, 64, 34, 20, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(262, 22), (134, 20), (64, 1), (34, 406), (20, 276), (10, 105), (1, 8)]
    (codeMat 460) (codeMat 417) (codeMat 177) false
    det460 det417 inv417
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3789_lower : 12 ≤ frozenWangTable.L0 (spanCodes [262, 134, 64, 34, 20, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3789_orbit
  simpa only [lower14] using h

theorem space3790_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 64, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 112), (129, 80), (64, 8), (33, 70), (16, 2), (8, 1), (2, 128)]
    (codeMat 98) (codeMat 305) (codeMat 305) false
    det98 det305 inv305
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3790_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3790_orbit
  simpa only [lower11] using h

theorem space3791_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 64, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 360), (132, 362), (64, 1), (33, 97), (21, 284), (8, 8), (2, 511)]
    (codeMat 468) (codeMat 407) (codeMat 405) false
    det468 det407 inv407
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3791_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3791_orbit
  simpa only [lower14] using h

theorem space3792_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 133, 65, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 384), (133, 104), (65, 128), (33, 406), (21, 97), (8, 130), (2, 8)]
    (codeMat 335) (codeMat 298) (codeMat 270) false
    det335 det298 inv298
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3792_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 65, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3792_orbit
  simpa only [lower14] using h

theorem space3793_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 133, 68, 36, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 128), (133, 96), (68, 488), (36, 130), (21, 97), (8, 511), (2, 8)]
    (codeMat 334) (codeMat 107) (codeMat 428) false
    det334 det107 inv107
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3793_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 36, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3793_orbit
  simpa only [lower14] using h

theorem space3794_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 68, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 511), (132, 509), (68, 510), (37, 392), (21, 264), (8, 384), (2, 360)]
    (codeMat 156) (codeMat 494) (codeMat 501) false
    det156 det494 inv494
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3794_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3794_orbit
  simpa only [lower14] using h

theorem space3795_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [260, 128, 65, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(260, 3), (128, 325), (65, 1), (36, 24), (20, 424), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 167) (codeMat 167) false
    det93 det167 inv167
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3795_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 65, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 10 space3795_orbit
  simpa only [lower10] using h

theorem space3796_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 69, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 130), (132, 139), (69, 278), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 214) (codeMat 122) (codeMat 460) false
    det214 det122 inv122
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3796_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3796_orbit
  simpa only [lower14] using h

theorem space3797_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 65, 33, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (128, 9), (65, 219), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 86) (codeMat 299) (codeMat 318) false
    det86 det299 inv299
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3797_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3797_orbit
  simpa only [lower11] using h

theorem space3798_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 68, 36, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (9, 256), (3, 360)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    det212 det98 inv98
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3798_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3798_orbit
  simpa only [lower14] using h

theorem space3799_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 65, 33, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 119), (133, 287), (65, 9), (33, 503), (21, 284), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 307) (codeMat 311) false
    det478 det307 inv307
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3799_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 65, 33, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3799_orbit
  simpa only [lower14] using h

theorem space3800_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [261, 133, 69, 37, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(261, 28), (133, 30), (69, 31), (37, 284), (21, 414), (9, 511), (3, 8)]
    (codeMat 396) (codeMat 473) (codeMat 409) false
    det396 det473 inv473
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3800_lower : 12 ≤ frozenWangTable.L0 (spanCodes [261, 133, 69, 37, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3800_orbit
  simpa only [lower14] using h

theorem space3801_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 132, 64, 32, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 9), (132, 265), (64, 128), (32, 8), (20, 97), (9, 130), (3, 511)]
    (codeMat 279) (codeMat 142) (codeMat 354) false
    det279 det142 inv142
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3801_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 64, 32, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3801_orbit
  simpa only [lower14] using h

theorem space3802_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 132, 64, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (132, 149), (64, 1), (36, 128), (17, 96), (8, 8), (2, 360)]
    (codeMat 212) (codeMat 163) (codeMat 165) false
    det212 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3802_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3802_orbit
  simpa only [lower14] using h

theorem space3803_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 128, 68, 36, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (128, 1), (68, 21), (36, 128), (17, 96), (8, 360), (2, 8)]
    (codeMat 204) (codeMat 99) (codeMat 172) false
    det204 det99 inv99
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3803_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3803_orbit
  simpa only [lower14] using h

theorem space3804_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 65, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (129, 208), (65, 216), (33, 198), (16, 2), (8, 3), (2, 128)]
    (codeMat 98) (codeMat 313) (codeMat 313) false
    det98 det313 inv313
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3804_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3804_orbit
  simpa only [lower11] using h

theorem space3805_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [259, 130, 65, 35, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(259, 104), (130, 128), (65, 384), (35, 97), (16, 130), (10, 406), (4, 8)]
    (codeMat 335) (codeMat 92) (codeMat 116) false
    det335 det92 inv92
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3805_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 130, 65, 35, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3805_orbit
  simpa only [lower14] using h

theorem space3806_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 129, 66, 33, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 278), (129, 126), (66, 119), (33, 406), (18, 511), (10, 503), (4, 130)]
    (codeMat 407) (codeMat 250) (codeMat 397) false
    det407 det250 inv250
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3806_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 33, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 14 space3806_orbit
  simpa only [lower14] using h

theorem space3807_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 129, 65, 34, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 324), (129, 326), (65, 325), (34, 416), (18, 432), (10, 424), (4, 256)]
    (codeMat 84) (codeMat 465) (codeMat 465) false
    det84 det465 inv465
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3807_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 34, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space3807_orbit
  simpa only [lower10] using h


end QiushiMatmul.FrozenWang
