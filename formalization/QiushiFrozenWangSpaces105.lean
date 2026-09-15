import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3360_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 132, 68, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 9), (132, 82), (68, 100), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    det86 det84 inv84
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3360_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 132, 68, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3360_orbit
  simpa only [lower11] using h

theorem space3361_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 133, 65, 37, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 511), (133, 97), (65, 130), (37, 488), (21, 104), (8, 128), (2, 8)]
    (codeMat 143) (codeMat 302) (codeMat 302) false
    det143 det302 inv302
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3361_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 133, 65, 37, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3361_orbit
  simpa only [lower14] using h

theorem space3362_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 80, 49, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 130), (145, 374), (80, 245), (49, 96), (8, 360), (4, 128), (2, 384)]
    (codeMat 93) (codeMat 241) (codeMat 489) false
    det93 det241 inv241
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3362_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 80, 49, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3362_orbit
  simpa only [lower14] using h

theorem space3363_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 145, 80, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (145, 28), (80, 480), (48, 384), (8, 256), (5, 1), (2, 3)]
    (codeMat 177) (codeMat 342) (codeMat 215) false
    det177 det342 inv342
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3363_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 80, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3363_orbit
  simpa only [lower14] using h

theorem space3364_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 144, 81, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 360), (144, 8), (81, 502), (48, 256), (8, 384), (5, 3), (2, 1)]
    (codeMat 177) (codeMat 334) (codeMat 442) false
    det177 det334 inv334
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3364_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 81, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3364_orbit
  simpa only [lower14] using h

theorem space3365_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 144, 80, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 384), (144, 8), (80, 264), (49, 509), (8, 360), (5, 3), (2, 1)]
    (codeMat 305) (codeMat 355) (codeMat 190) false
    det305 det355 inv355
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3365_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 80, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3365_orbit
  simpa only [lower14] using h

theorem space3366_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 65, 49, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (129, 61), (65, 2), (49, 208), (8, 128), (5, 32), (2, 40)]
    (codeMat 141) (codeMat 426) (codeMat 335) false
    det141 det426 inv426
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3366_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 49, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3366_orbit
  simpa only [lower11] using h

theorem space3367_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 145, 65, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 219), (145, 52), (65, 130), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 143) (codeMat 172) (codeMat 99) false
    det143 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3367_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 145, 65, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3367_orbit
  simpa only [lower11] using h

theorem space3368_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 64, 48, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 28), (129, 30), (64, 3), (48, 128), (9, 216), (4, 32), (3, 40)]
    (codeMat 140) (codeMat 409) (codeMat 473) false
    det140 det409 inv409
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3368_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 48, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3368_orbit
  simpa only [lower11] using h

theorem space3369_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [258, 130, 69, 34, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(258, 137), (130, 128), (69, 283), (34, 138), (18, 130), (10, 170)]
    (codeMat 342) (codeMat 125) (codeMat 348) false
    det342 det125 inv125
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3369_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 69, 34, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 43 space3369_orbit
  simpa only [lower43] using h

theorem space3370_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 65, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 235), (129, 381), (65, 511), (34, 232), (18, 360), (10, 488), (7, 8)]
    (codeMat 142) (codeMat 239) (codeMat 351) false
    det142 det239 inv239
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3370_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 65, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3370_orbit
  simpa only [lower14] using h

theorem space3371_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 66, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 287), (129, 126), (66, 119), (33, 414), (18, 511), (10, 503), (7, 130)]
    (codeMat 407) (codeMat 254) (codeMat 443) false
    det407 det254 inv254
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3371_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3371_orbit
  simpa only [lower14] using h

theorem space3372_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 65, 35, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 488), (130, 128), (65, 256), (35, 503), (16, 130), (10, 276), (7, 8)]
    (codeMat 335) (codeMat 372) (codeMat 93) false
    det335 det372 inv372
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3372_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 35, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 14 space3372_orbit
  simpa only [lower14] using h

theorem space3373_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [258, 130, 65, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(258, 10), (130, 3), (65, 5), (50, 88), (10, 344), (6, 8)]
    (codeMat 141) (codeMat 115) (codeMat 492) false
    det141 det115 inv115
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3373_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 25 space3373_orbit
  simpa only [lower25] using h

theorem space3374_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 129, 67, 33, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 503), (129, 414), (67, 235), (33, 480), (18, 384), (10, 232), (6, 8)]
    (codeMat 207) (codeMat 445) (codeMat 478) false
    det207 det445 inv445
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3374_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 129, 67, 33, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 14 space3374_orbit
  simpa only [lower14] using h

theorem space3375_orbit :
    frozenWangTable.OrbitImage 25 (spanCodes [258, 146, 66, 34, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 25 [(258, 344), (146, 256), (66, 347), (34, 336), (10, 338), (5, 5)]
    (codeMat 470) (codeMat 169) (codeMat 225) true
    det470 det169 inv169
    (by rw [basis25]; decide +kernel)
    (by rw [basis25]; decide +kernel)

theorem space3375_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 146, 66, 34, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 25 space3375_orbit
  simpa only [lower25] using h

theorem space3376_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 65, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 361), (130, 1), (65, 3), (35, 406), (18, 8), (10, 138), (5, 511)]
    (codeMat 477) (codeMat 267) (codeMat 282) false
    det477 det267 inv267
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3376_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 65, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3376_orbit
  simpa only [lower14] using h

theorem space3377_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 65, 34, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 235), (131, 284), (65, 511), (34, 387), (18, 3), (10, 259), (5, 130)]
    (codeMat 163) (codeMat 351) (codeMat 239) false
    det163 det351 inv351
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3377_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 65, 34, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3377_orbit
  simpa only [lower14] using h

theorem space3378_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 130, 67, 33, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 138), (130, 8), (67, 105), (33, 508), (18, 1), (10, 361), (5, 511)]
    (codeMat 491) (codeMat 102) (codeMat 156) false
    det491 det102 inv102
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3378_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 33, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3378_orbit
  simpa only [lower14] using h

theorem space3379_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 131, 67, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 373), (131, 97), (67, 105), (32, 3), (18, 360), (10, 361), (5, 511)]
    (codeMat 482) (codeMat 230) (codeMat 159) false
    det482 det230 inv230
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3379_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3379_orbit
  simpa only [lower14] using h

theorem space3380_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 112), (128, 8), (64, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 98) (codeMat 354) (codeMat 142) false
    det98 det354 inv354
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3380_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3380_orbit
  simpa only [lower11] using h

theorem space3381_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 66, 32, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 68), (128, 1), (66, 70), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    det84 det330 inv330
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3381_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 32, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3381_orbit
  simpa only [lower11] using h

theorem space3382_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [257, 129, 65, 52, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(257, 42), (129, 10), (65, 2), (52, 283), (9, 128), (3, 9)]
    (codeMat 229) (codeMat 318) (codeMat 299) false
    det229 det318 inv318
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3382_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 52, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 43 space3382_orbit
  simpa only [lower43] using h

theorem space3383_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [257, 144, 65, 37, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(257, 306), (144, 3), (65, 130), (37, 274), (9, 128), (3, 9)]
    (codeMat 254) (codeMat 282) (codeMat 267) false
    det254 det282 inv282
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3383_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 65, 37, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 43 space3383_orbit
  simpa only [lower43] using h

theorem space3384_orbit :
    frozenWangTable.OrbitImage 43 (spanCodes [257, 145, 65, 36, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 43 [(257, 139), (145, 400), (65, 130), (36, 3), (9, 2), (3, 432)]
    (codeMat 443) (codeMat 172) (codeMat 99) false
    det443 det172 inv172
    (by rw [basis43]; decide +kernel)
    (by rw [basis43]; decide +kernel)

theorem space3384_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 145, 65, 36, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 43 space3384_orbit
  simpa only [lower43] using h

theorem space3385_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 65, 37, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 353), (133, 413), (65, 9), (37, 97), (21, 414), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 275) (codeMat 275) false
    det478 det275 inv275
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3385_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 37, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3385_orbit
  simpa only [lower14] using h

theorem space3386_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 133, 65, 36, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 138), (133, 276), (65, 8), (36, 3), (20, 363), (9, 1), (3, 511)]
    (codeMat 491) (codeMat 181) (codeMat 423) false
    det491 det181 inv181
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3386_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 133, 65, 36, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3386_orbit
  simpa only [lower14] using h

theorem space3387_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 144, 80, 49, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 387), (144, 511), (80, 381), (49, 352), (9, 360), (5, 384), (3, 128)]
    (codeMat 85) (codeMat 247) (codeMat 379) false
    det85 det247 inv247
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3387_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 80, 49, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3387_orbit
  simpa only [lower14] using h

theorem space3388_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 144, 81, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 232), (144, 511), (81, 287), (48, 130), (9, 3), (5, 384), (3, 256)]
    (codeMat 99) (codeMat 415) (codeMat 253) false
    det99 det415 inv415
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3388_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 144, 81, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3388_orbit
  simpa only [lower14] using h

theorem space3389_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [258, 134, 66, 36, 22, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(258, 252), (134, 483), (66, 404), (36, 511), (22, 227), (10, 276), (1, 130)]
    (codeMat 407) (codeMat 428) (codeMat 107) false
    det407 det428 inv428
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3389_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 134, 66, 36, 22, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3389_orbit
  simpa only [lower14] using h

theorem space3390_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3390_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3390_orbit
  simpa only [lower3] using h

theorem space3391_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 3), (129, 68), (64, 1), (33, 88), (16, 32), (8, 8), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 165) (codeMat 163) false
    det84 det165 inv165
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3391_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space3391_orbit
  simpa only [lower3] using h


end QiushiMatmul.FrozenWang
