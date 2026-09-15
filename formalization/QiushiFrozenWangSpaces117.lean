import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3744_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [260, 132, 69, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(260, 390), (132, 391), (69, 197), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 84) (codeMat 499) (codeMat 382) false
    det84 det499 inv499
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3744_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 132, 69, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3744_orbit
  simpa only [lower17] using h

theorem space3745_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [260, 133, 68, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(260, 63), (133, 374), (68, 228), (37, 312), (20, 112), (9, 32), (3, 128)]
    (codeMat 94) (codeMat 500) (codeMat 94) false
    det94 det500 inv500
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3745_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3745_orbit
  simpa only [lower17] using h

theorem space3746_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [273, 145, 81, 49, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(273, 273), (145, 274), (81, 272), (49, 316), (8, 32), (2, 438)]
    (codeMat 468) (codeMat 468) (codeMat 87) false
    det468 det468 inv468
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3746_lower : 14 ≤ frozenWangTable.L0 (spanCodes [273, 145, 81, 49, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 55 space3746_orbit
  simpa only [lower55] using h

theorem space3747_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [260, 129, 68, 33, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(260, 63), (129, 402), (68, 228), (33, 312), (21, 208), (8, 32), (2, 128)]
    (codeMat 87) (codeMat 372) (codeMat 93) false
    det87 det372 inv372
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3747_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 129, 68, 33, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3747_orbit
  simpa only [lower17] using h

theorem space3748_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 129, 69, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 323), (129, 450), (69, 197), (33, 408), (20, 80), (8, 360), (2, 128)]
    (codeMat 93) (codeMat 117) (codeMat 380) false
    det93 det117 inv117
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3748_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 69, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3748_orbit
  simpa only [lower17] using h

theorem space3749_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 130, 68, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 316), (130, 32), (68, 287), (39, 133), (21, 47), (10, 168)]
    (codeMat 342) (codeMat 348) (codeMat 125) true
    det342 det348 inv348
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3749_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 130, 68, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3749_orbit
  simpa only [lower55] using h

theorem space3750_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 135, 65, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 1), (135, 134), (65, 3), (37, 136), (23, 304), (10, 408)]
    (codeMat 85) (codeMat 157) (codeMat 486) false
    det85 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3750_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 135, 65, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3750_orbit
  simpa only [lower55] using h

theorem space3751_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 67, 33, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 129), (129, 196), (67, 263), (33, 456), (16, 32), (10, 312), (7, 128)]
    (codeMat 85) (codeMat 205) (codeMat 242) false
    det85 det205 inv205
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3751_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 67, 33, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space3751_orbit
  simpa only [lower17] using h

theorem space3752_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [256, 131, 65, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(256, 219), (131, 502), (65, 63), (34, 408), (19, 112), (10, 440), (7, 128)]
    (codeMat 87) (codeMat 253) (codeMat 415) false
    det87 det253 inv253
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3752_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 131, 65, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space3752_orbit
  simpa only [lower17] using h

theorem space3753_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 130, 64, 38, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 437), (130, 438), (64, 2), (38, 408), (17, 272), (10, 304)]
    (codeMat 156) (codeMat 412) (codeMat 111) false
    det156 det412 inv412
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3753_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 38, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3753_orbit
  simpa only [lower55] using h

theorem space3754_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 66, 35, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 91), (131, 301), (66, 329), (35, 280), (18, 360), (10, 328), (5, 128)]
    (codeMat 86) (codeMat 167) (codeMat 167) false
    det86 det167 inv167
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3754_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 66, 35, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 17 space3754_orbit
  simpa only [lower17] using h

theorem space3755_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 194, 32, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 437), (194, 408), (32, 2), (17, 272), (10, 304), (6, 438)]
    (codeMat 215) (codeMat 212) (codeMat 86) true
    det215 det212 inv212
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3755_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 194, 32, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space3755_orbit
  simpa only [lower55] using h

theorem space3756_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 66, 35, 17, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 129), (131, 451), (66, 263), (35, 328), (17, 280), (10, 312), (6, 128)]
    (codeMat 93) (codeMat 95) (codeMat 244) false
    det93 det95 inv95
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3756_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 66, 35, 17, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space3756_orbit
  simpa only [lower17] using h

theorem space3757_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 65, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 391), (131, 69), (65, 1), (35, 312), (18, 360), (10, 328), (6, 128)]
    (codeMat 85) (codeMat 423) (codeMat 181) false
    det85 det423 inv423
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3757_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 65, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space3757_orbit
  simpa only [lower17] using h

theorem space3758_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 67, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (128, 2), (67, 436), (38, 139), (19, 306), (10, 404)]
    (codeMat 444) (codeMat 116) (codeMat 92) false
    det444 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space3758_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 67, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space3758_orbit
  simpa only [lower55] using h

theorem space3759_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 131, 66, 35, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 502), (131, 100), (66, 329), (35, 240), (18, 32), (10, 328), (6, 128)]
    (codeMat 94) (codeMat 417) (codeMat 177) false
    det94 det417 inv417
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3759_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 66, 35, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 17 space3759_orbit
  simpa only [lower17] using h

theorem space3760_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 67, 33, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 502), (129, 301), (67, 329), (33, 112), (18, 360), (10, 328), (7, 128)]
    (codeMat 87) (codeMat 419) (codeMat 183) false
    det87 det419 inv419
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3760_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 67, 33, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 17 space3760_orbit
  simpa only [lower17] using h

theorem space3761_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 133, 68, 33, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 451), (133, 450), (68, 196), (33, 280), (20, 208), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    det84 det116 inv116
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3761_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 133, 68, 33, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3761_orbit
  simpa only [lower17] using h

theorem space3762_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 133, 68, 33, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 329), (133, 374), (68, 100), (33, 328), (21, 240), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    det95 det212 inv212
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3762_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 133, 68, 33, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3762_orbit
  simpa only [lower17] using h

theorem space3763_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 216), (68, 88), (32, 3), (20, 28), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 165) (codeMat 163) false
    det266 det165 inv165
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3763_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3763_orbit
  simpa only [lower11] using h

theorem space3764_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 68, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 216), (68, 88), (36, 3), (20, 60), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 165) (codeMat 163) false
    det267 det165 inv165
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3764_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 68, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3764_orbit
  simpa only [lower11] using h

theorem space3765_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 196), (129, 68), (33, 28), (16, 8), (8, 32), (4, 3), (2, 1)]
    (codeMat 273) (codeMat 102) (codeMat 156) false
    det273 det102 inv102
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3765_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3765_orbit
  simpa only [lower11] using h

theorem space3766_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 32, 16, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (129, 240), (32, 2), (16, 3), (9, 54), (5, 32), (3, 40)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    det266 det122 inv122
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3766_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 32, 16, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3766_orbit
  simpa only [lower11] using h

theorem space3767_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 240), (129, 112), (33, 43), (16, 9), (8, 54), (5, 40), (2, 8)]
    (codeMat 267) (codeMat 110) (codeMat 444) false
    det267 det110 inv110
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3767_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3767_orbit
  simpa only [lower11] using h

theorem space3768_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 129, 33, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 128), (129, 196), (33, 20), (17, 28), (8, 32), (4, 2), (2, 3)]
    (codeMat 273) (codeMat 114) (codeMat 204) false
    det273 det114 inv114
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3768_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 129, 33, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3768_orbit
  simpa only [lower11] using h

theorem space3769_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 128, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (128, 8), (68, 22), (20, 70), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 298) (codeMat 270) false
    det161 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3769_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3769_orbit
  simpa only [lower11] using h

theorem space3770_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 96, 18, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 3), (160, 29), (96, 28), (18, 360), (10, 352), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 230) (codeMat 159) false
    det84 det230 inv230
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3770_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 96, 18, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 14 space3770_orbit
  simpa only [lower14] using h

theorem space3771_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 161, 96, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 361), (161, 247), (96, 97), (17, 386), (9, 256), (5, 1), (3, 2)]
    (codeMat 241) (codeMat 468) (codeMat 87) false
    det241 det468 inv468
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3771_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 161, 96, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3771_orbit
  simpa only [lower14] using h

theorem space3772_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 65, 17, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 54), (128, 9), (65, 2), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 141) (codeMat 298) (codeMat 270) false
    det141 det298 inv298
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3772_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 17, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3772_orbit
  simpa only [lower11] using h

theorem space3773_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [256, 160, 96, 17, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(256, 2), (160, 148), (96, 149), (17, 96), (8, 360), (4, 128), (2, 256)]
    (codeMat 92) (codeMat 225) (codeMat 169) false
    det92 det225 inv225
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3773_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 160, 96, 17, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3773_orbit
  simpa only [lower14] using h

theorem space3774_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [260, 132, 68, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(260, 54), (132, 30), (68, 22), (20, 198), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    det161 det314 inv314
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3774_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3774_orbit
  simpa only [lower11] using h

theorem space3775_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [274, 144, 66, 48, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(274, 180), (144, 32), (66, 76), (48, 128), (10, 68), (6, 2), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3775_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 144, 66, 48, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3775_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
