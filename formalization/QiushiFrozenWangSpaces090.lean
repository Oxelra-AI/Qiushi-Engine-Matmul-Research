import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2880_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [64, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(64, 16), (32, 1), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    det98 det140 inv140
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space2880_lower : 17 ≤ frozenWangTable.L0 (spanCodes [64, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space2880_orbit
  simpa only [lower433] using h

theorem space2881_orbit :
    frozenWangTable.OrbitImage 433 (spanCodes [66, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 433 [(66, 274), (34, 259), (10, 258)]
    (codeMat 114) (codeMat 172) (codeMat 99) false
    det114 det172 inv172
    (by rw [basis433]; decide +kernel)
    (by rw [basis433]; decide +kernel)

theorem space2881_lower : 17 ≤ frozenWangTable.L0 (spanCodes [66, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 433 space2881_orbit
  simpa only [lower433] using h

theorem space2882_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [131, 96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(131, 43), (96, 283), (18, 1), (10, 33)]
    (codeMat 187) (codeMat 267) (codeMat 282) true
    det187 det267 inv267
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2882_lower : 17 ≤ frozenWangTable.L0 (spanCodes [131, 96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space2882_orbit
  simpa only [lower295] using h

theorem space2883_orbit :
    frozenWangTable.OrbitImage 290 (spanCodes [160, 96, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 290 [(160, 10), (96, 42), (16, 1), (10, 69)]
    (codeMat 98) (codeMat 99) (codeMat 172) false
    det98 det99 inv99
    (by rw [basis290]; decide +kernel)
    (by rw [basis290]; decide +kernel)

theorem space2883_lower : 17 ≤ frozenWangTable.L0 (spanCodes [160, 96, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 290 space2883_orbit
  simpa only [lower290] using h

theorem space2884_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [165, 96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(165, 270), (96, 170), (18, 1), (10, 261)]
    (codeMat 115) (codeMat 359) (codeMat 174) false
    det115 det359 inv359
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2884_lower : 17 ≤ frozenWangTable.L0 (spanCodes [165, 96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2884_orbit
  simpa only [lower315] using h

theorem space2885_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [180, 96, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(180, 430), (96, 160), (9, 260), (3, 1)]
    (codeMat 177) (codeMat 482) (codeMat 143) false
    det177 det482 inv482
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2885_lower : 17 ≤ frozenWangTable.L0 (spanCodes [180, 96, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 315 space2885_orbit
  simpa only [lower315] using h

theorem space2886_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [257, 96, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(257, 33), (96, 42), (10, 315), (5, 32)]
    (codeMat 117) (codeMat 143) (codeMat 482) true
    det117 det143 inv143
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2886_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 96, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 295 space2886_orbit
  simpa only [lower295] using h

theorem space2887_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [260, 96, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(260, 1), (96, 42), (10, 272), (1, 32)]
    (codeMat 85) (codeMat 140) (codeMat 98) true
    det85 det140 inv140
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2887_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 96, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 295 space2887_orbit
  simpa only [lower295] using h

theorem space2888_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [259, 96, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(259, 304), (96, 42), (10, 315), (4, 32)]
    (codeMat 103) (codeMat 171) (codeMat 485) true
    det103 det171 inv171
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2888_lower : 17 ≤ frozenWangTable.L0 (spanCodes [259, 96, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 295 space2888_orbit
  simpa only [lower295] using h

theorem space2889_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [262, 96, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(262, 283), (96, 42), (10, 272), (1, 32)]
    (codeMat 87) (codeMat 172) (codeMat 99) true
    det87 det172 inv172
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2889_lower : 17 ≤ frozenWangTable.L0 (spanCodes [262, 96, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 295 space2889_orbit
  simpa only [lower295] using h

theorem space2890_orbit :
    frozenWangTable.OrbitImage 434 (spanCodes [288, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 434 [(288, 1), (96, 17), (10, 283)]
    (codeMat 102) (codeMat 141) (codeMat 226) false
    det102 det141 inv141
    (by rw [basis434]; decide +kernel)
    (by rw [basis434]; decide +kernel)

theorem space2890_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 434 space2890_orbit
  simpa only [lower434] using h

theorem space2891_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [256, 66, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(256, 1), (66, 259), (34, 264), (10, 280)]
    (codeMat 84) (codeMat 141) (codeMat 226) false
    det84 det141 inv141
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space2891_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 66, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 282 space2891_orbit
  simpa only [lower282] using h

theorem space2892_orbit :
    frozenWangTable.OrbitImage 282 (spanCodes [258, 64, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 282 [(258, 258), (64, 1), (32, 16), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    det84 det161 inv161
    (by rw [basis282]; decide +kernel)
    (by rw [basis282]; decide +kernel)

theorem space2892_lower : 17 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 282 space2892_orbit
  simpa only [lower282] using h

theorem space2893_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [292, 96, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(292, 260), (96, 160), (17, 10), (10, 11)]
    (codeMat 275) (codeMat 282) (codeMat 267) false
    det275 det282 inv282
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2893_lower : 17 ≤ frozenWangTable.L0 (spanCodes [292, 96, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2893_orbit
  simpa only [lower315] using h

theorem space2894_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [272, 144, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(272, 33), (144, 32), (96, 42), (10, 283)]
    (codeMat 244) (codeMat 461) (codeMat 234) false
    det244 det461 inv461
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2894_lower : 17 ≤ frozenWangTable.L0 (spanCodes [272, 144, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space2894_orbit
  simpa only [lower295] using h

theorem space2895_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [308, 178, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(308, 11), (178, 10), (96, 430), (10, 160)]
    (codeMat 213) (codeMat 124) (codeMat 124) false
    det213 det124 inv124
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2895_lower : 17 ≤ frozenWangTable.L0 (spanCodes [308, 178, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2895_orbit
  simpa only [lower315] using h

theorem space2896_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [384, 96, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(384, 1), (96, 42), (16, 32), (10, 272)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    det84 det396 inv396
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2896_lower : 17 ≤ frozenWangTable.L0 (spanCodes [384, 96, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space2896_orbit
  simpa only [lower295] using h

theorem space2897_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [274, 128, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(274, 272), (128, 32), (96, 42), (10, 283)]
    (codeMat 230) (codeMat 233) (codeMat 233) false
    det230 det233 inv233
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2897_lower : 17 ≤ frozenWangTable.L0 (spanCodes [274, 128, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space2897_orbit
  simpa only [lower295] using h

theorem space2898_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [386, 96, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(386, 283), (96, 42), (16, 32), (10, 272)]
    (codeMat 86) (codeMat 428) (codeMat 107) false
    det86 det428 inv428
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2898_lower : 17 ≤ frozenWangTable.L0 (spanCodes [386, 96, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 295 space2898_orbit
  simpa only [lower295] using h

theorem space2899_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [309, 160, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(309, 421), (160, 170), (96, 430), (10, 160)]
    (codeMat 215) (codeMat 348) (codeMat 125) false
    det215 det348 inv348
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2899_lower : 17 ≤ frozenWangTable.L0 (spanCodes [309, 160, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2899_orbit
  simpa only [lower315] using h

theorem space2900_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [390, 71, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(390, 1), (71, 10), (39, 430), (10, 170)]
    (codeMat 397) (codeMat 442) (codeMat 334) false
    det397 det442 inv442
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2900_lower : 17 ≤ frozenWangTable.L0 (spanCodes [390, 71, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2900_orbit
  simpa only [lower315] using h

theorem space2901_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [417, 96, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(417, 270), (96, 170), (17, 10), (10, 11)]
    (codeMat 339) (codeMat 318) (codeMat 299) false
    det339 det318 inv318
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space2901_lower : 17 ≤ frozenWangTable.L0 (spanCodes [417, 96, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 315 space2901_orbit
  simpa only [lower315] using h

theorem space2902_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [96, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(96, 264), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    det273 det84 inv84
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2902_lower : 16 ≤ frozenWangTable.L0 (spanCodes [96, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2902_orbit
  simpa only [lower269] using h

theorem space2903_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [96, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(96, 297), (9, 32), (5, 1), (3, 2)]
    (codeMat 345) (codeMat 468) (codeMat 87) false
    det345 det468 inv468
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2903_lower : 16 ≤ frozenWangTable.L0 (spanCodes [96, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space2903_orbit
  simpa only [lower269] using h

theorem space2904_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [96, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(96, 265), (9, 32), (4, 1), (3, 2)]
    (codeMat 281) (codeMat 212) (codeMat 86) false
    det281 det212 inv212
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2904_lower : 16 ≤ frozenWangTable.L0 (spanCodes [96, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 269 space2904_orbit
  simpa only [lower269] using h

theorem space2905_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [96, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(96, 296), (8, 32), (5, 1), (2, 2)]
    (codeMat 273) (codeMat 340) (codeMat 85) false
    det273 det340 inv340
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2905_lower : 16 ≤ frozenWangTable.L0 (spanCodes [96, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2905_orbit
  simpa only [lower269] using h

theorem space2906_orbit :
    frozenWangTable.OrbitImage 255 (spanCodes [96, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 255 [(96, 96), (16, 1), (8, 8), (2, 2)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    det266 det266 inv266
    (by rw [basis255]; decide +kernel)
    (by rw [basis255]; decide +kernel)

theorem space2906_lower : 16 ≤ frozenWangTable.L0 (spanCodes [96, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 255 space2906_orbit
  simpa only [lower255] using h

theorem space2907_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [67, 35, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(67, 170), (35, 33), (10, 42), (7, 32)]
    (codeMat 459) (codeMat 158) (codeMat 358) false
    det459 det158 inv158
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2907_lower : 16 ≤ frozenWangTable.L0 (spanCodes [67, 35, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 292 space2907_orbit
  simpa only [lower292] using h

theorem space2908_orbit :
    frozenWangTable.OrbitImage 292 (spanCodes [65, 33, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 292 [(65, 128), (33, 11), (10, 42), (6, 32)]
    (codeMat 331) (codeMat 190) (codeMat 355) false
    det331 det190 inv190
    (by rw [basis292]; decide +kernel)
    (by rw [basis292]; decide +kernel)

theorem space2908_lower : 16 ≤ frozenWangTable.L0 (spanCodes [65, 33, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 292 space2908_orbit
  simpa only [lower292] using h

theorem space2909_orbit :
    frozenWangTable.OrbitImage 264 (spanCodes [80, 48, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 264 [(80, 12), (48, 2), (8, 1), (2, 256)]
    (codeMat 98) (codeMat 417) (codeMat 177) false
    det98 det417 inv417
    (by rw [basis264]; decide +kernel)
    (by rw [basis264]; decide +kernel)

theorem space2909_lower : 16 ≤ frozenWangTable.L0 (spanCodes [80, 48, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 264 space2909_orbit
  simpa only [lower264] using h

theorem space2910_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [85, 53, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(85, 85), (53, 35), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 419) (codeMat 183) false
    det267 det419 inv419
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space2910_lower : 16 ≤ frozenWangTable.L0 (spanCodes [85, 53, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 267 space2910_orbit
  simpa only [lower267] using h

theorem space2911_orbit :
    frozenWangTable.OrbitImage 269 (spanCodes [128, 96, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 269 [(128, 1), (96, 264), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    det140 det266 inv266
    (by rw [basis269]; decide +kernel)
    (by rw [basis269]; decide +kernel)

theorem space2911_lower : 16 ≤ frozenWangTable.L0 (spanCodes [128, 96, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 269 space2911_orbit
  simpa only [lower269] using h


end QiushiMatmul.FrozenWang
