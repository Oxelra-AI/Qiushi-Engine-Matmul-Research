import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3040_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 69, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 96), (128, 9), (69, 104), (37, 224), (23, 31), (10, 252)]
    (codeMat 116) (codeMat 346) (codeMat 459) true
    det116 det346 inv346
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3040_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 69, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3040_orbit
  simpa only [lower35] using h

theorem space3041_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 65, 33, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 150), (130, 2), (65, 3), (33, 232), (18, 128), (10, 136)]
    (codeMat 213) (codeMat 313) (codeMat 313) false
    det213 det313 inv313
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3041_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 65, 33, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3041_orbit
  simpa only [lower35] using h

theorem space3042_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 69, 37, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 126), (128, 9), (69, 245), (37, 232), (16, 8), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    det214 det355 inv355
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3042_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 69, 37, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3042_orbit
  simpa only [lower35] using h

theorem space3043_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 130, 67, 35, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 148), (130, 2), (67, 20), (35, 252), (16, 3), (10, 28)]
    (codeMat 111) (codeMat 298) (codeMat 270) true
    det111 det298 inv298
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3043_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 130, 67, 35, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3043_orbit
  simpa only [lower35] using h

theorem space3044_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 147, 67, 35, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 105), (147, 30), (67, 235), (35, 96), (10, 232), (4, 8)]
    (codeMat 207) (codeMat 157) (codeMat 486) false
    det207 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3044_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 147, 67, 35, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3044_orbit
  simpa only [lower35] using h

theorem space3045_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [385, 80, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(385, 22), (80, 255), (48, 3), (9, 9), (5, 130), (3, 128)]
    (codeMat 267) (codeMat 443) (codeMat 254) true
    det267 det443 inv443
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3045_lower : 15 ≤ frozenWangTable.L0 (spanCodes [385, 80, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space3045_orbit
  simpa only [lower35] using h

theorem space3046_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [276, 128, 65, 33, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(276, 20), (128, 130), (65, 1), (33, 96), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    det85 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3046_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 128, 65, 33, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space3046_orbit
  simpa only [lower35] using h

theorem space3047_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [276, 134, 68, 36, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(276, 245), (134, 430), (68, 186), (36, 320), (10, 160), (1, 16)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    det206 det412 inv412
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3047_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 134, 68, 36, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space3047_orbit
  simpa only [lower65] using h

theorem space3048_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 176, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 119), (176, 252), (96, 28), (10, 104), (4, 9), (1, 8)]
    (codeMat 185) (codeMat 188) (codeMat 103) true
    det185 det188 inv188
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3048_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 176, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3048_orbit
  simpa only [lower35] using h

theorem space3049_orbit :
    frozenWangTable.OrbitImage 74 (spanCodes [259, 132, 64, 32, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 74 [(259, 366), (132, 223), (64, 1), (32, 192), (22, 255), (10, 356)]
    (codeMat 188) (codeMat 165) (codeMat 163) false
    det188 det165 inv165
    (by rw [basis74]; decide +kernel)
    (by rw [basis74]; decide +kernel)

theorem space3049_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 132, 64, 32, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 74 space3049_orbit
  simpa only [lower74] using h

theorem space3050_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 128, 66, 34, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 274), (128, 219), (66, 374), (34, 208), (17, 408), (10, 240), (4, 128)]
    (codeMat 87) (codeMat 122) (codeMat 460) false
    det87 det122 inv122
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3050_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 66, 34, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space3050_orbit
  simpa only [lower17] using h

theorem space3051_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 132, 68, 36, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 69), (132, 450), (68, 68), (36, 360), (21, 80), (8, 32), (2, 128)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    det85 det340 inv340
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3051_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 132, 68, 36, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 17 space3051_orbit
  simpa only [lower17] using h

theorem space3052_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [261, 129, 69, 37, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(261, 374), (129, 191), (69, 429), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 87) (codeMat 499) (codeMat 382) false
    det87 det499 inv499
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space3052_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 129, 69, 37, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 17 space3052_orbit
  simpa only [lower17] using h

theorem space3053_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 64, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 34), (128, 54), (64, 9), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 141) (codeMat 177) (codeMat 417) false
    det141 det177 inv177
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3053_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3053_orbit
  simpa only [lower11] using h

theorem space3054_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 64, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 2), (130, 54), (64, 1), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 177) (codeMat 417) false
    det140 det177 inv177
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3054_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3054_orbit
  simpa only [lower11] using h

theorem space3055_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [257, 129, 65, 33, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(257, 11), (129, 52), (65, 2), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 141) (codeMat 172) (codeMat 99) false
    det141 det172 inv172
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3055_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 11 space3055_orbit
  simpa only [lower11] using h

theorem space3056_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 65, 33, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 9), (128, 54), (65, 3), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 141) (codeMat 157) (codeMat 486) false
    det141 det157 inv157
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3056_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3056_orbit
  simpa only [lower11] using h

theorem space3057_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [274, 146, 64, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(274, 508), (146, 511), (64, 2), (32, 256), (10, 184), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 410) (codeMat 331) false
    det140 det410 inv410
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3057_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 146, 64, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3057_orbit
  simpa only [lower10] using h

theorem space3058_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 144, 64, 32, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 324), (144, 325), (64, 2), (32, 256), (10, 168), (6, 8), (1, 16)]
    (codeMat 140) (codeMat 394) (codeMat 330) false
    det140 det394 inv394
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3058_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 144, 64, 32, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3058_orbit
  simpa only [lower10] using h

theorem space3059_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 128, 65, 33, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 3), (128, 511), (65, 2), (33, 136), (20, 224), (9, 128), (3, 360)]
    (codeMat 213) (codeMat 190) (codeMat 355) false
    det213 det190 inv190
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3059_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 128, 65, 33, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 14 space3059_orbit
  simpa only [lower14] using h

theorem space3060_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 128, 68, 36, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 9), (128, 54), (68, 100), (36, 8), (21, 240), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    det95 det212 inv212
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3060_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 11 space3060_orbit
  simpa only [lower11] using h

theorem space3061_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 129, 64, 32, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 128), (129, 96), (64, 8), (32, 2), (20, 149), (8, 1), (2, 360)]
    (codeMat 354) (codeMat 163) (codeMat 165) false
    det354 det163 inv163
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3061_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 129, 64, 32, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3061_orbit
  simpa only [lower14] using h

theorem space3062_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [260, 133, 68, 36, 20, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(260, 1), (133, 149), (68, 510), (36, 8), (20, 264), (8, 384), (2, 360)]
    (codeMat 157) (codeMat 206) (codeMat 498) false
    det157 det206 inv206
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3062_lower : 12 ≤ frozenWangTable.L0 (spanCodes [260, 133, 68, 36, 20, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 14 space3062_orbit
  simpa only [lower14] using h

theorem space3063_orbit :
    frozenWangTable.OrbitImage 14 (spanCodes [257, 130, 64, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 14 [(257, 362), (130, 1), (64, 511), (32, 128), (18, 8), (10, 392), (5, 360)]
    (codeMat 157) (codeMat 107) (codeMat 428) false
    det157 det107 inv107
    (by rw [basis14]; decide +kernel)
    (by rw [basis14]; decide +kernel)

theorem space3063_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 14 space3063_orbit
  simpa only [lower14] using h

theorem space3064_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 64, 32, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 8), (130, 216), (64, 32), (32, 1), (16, 3), (10, 196), (6, 128)]
    (codeMat 98) (codeMat 86) (codeMat 212) false
    det98 det86 inv86
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3064_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 32, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 11 space3064_orbit
  simpa only [lower11] using h

theorem space3065_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 130, 66, 34, 16, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 32), (130, 216), (66, 240), (34, 196), (16, 3), (10, 198), (5, 128)]
    (codeMat 98) (codeMat 346) (codeMat 459) false
    det98 det346 inv346
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3065_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 34, 16, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 11 space3065_orbit
  simpa only [lower11] using h

theorem space3066_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [257, 131, 64, 32, 18, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(257, 257), (131, 326), (64, 325), (32, 8), (18, 432), (10, 424), (5, 256)]
    (codeMat 85) (codeMat 213) (codeMat 470) false
    det85 det213 inv213
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3066_lower : 12 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 32, 18, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 10 space3066_orbit
  simpa only [lower10] using h

theorem space3067_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 131, 64, 32, 17, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 208), (131, 240), (64, 40), (32, 130), (17, 198), (10, 197), (4, 128)]
    (codeMat 99) (codeMat 241) (codeMat 489) false
    det99 det241 inv241
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3067_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 17, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 11 space3067_orbit
  simpa only [lower11] using h

theorem space3068_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [258, 130, 67, 35, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(258, 324), (130, 1), (67, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    det93 det331 inv331
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3068_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 67, 35, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 10 space3068_orbit
  simpa only [lower10] using h

theorem space3069_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [259, 128, 64, 32, 17, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(259, 91), (128, 54), (64, 63), (32, 216), (17, 112), (10, 120), (7, 128)]
    (codeMat 95) (codeMat 253) (codeMat 415) false
    det95 det253 inv253
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3069_lower : 12 ≤ frozenWangTable.L0 (spanCodes [259, 128, 64, 32, 17, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space3069_orbit
  simpa only [lower11] using h

theorem space3070_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 130, 66, 34, 16, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 240), (130, 216), (66, 248), (34, 198), (16, 3), (10, 199), (7, 128)]
    (codeMat 98) (codeMat 379) (codeMat 247) false
    det98 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3070_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 34, 16, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space3070_orbit
  simpa only [lower11] using h

theorem space3071_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [258, 128, 66, 34, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(258, 198), (128, 3), (66, 199), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 84) (codeMat 379) (codeMat 247) false
    det84 det379 inv379
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3071_lower : 12 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 11 space3071_orbit
  simpa only [lower11] using h


end QiushiMatmul.FrozenWang
