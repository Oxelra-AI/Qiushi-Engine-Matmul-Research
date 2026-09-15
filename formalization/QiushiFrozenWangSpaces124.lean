import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3968_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [131, 65, 32, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(131, 10), (65, 1), (32, 260), (21, 170)]
    (codeMat 461) (codeMat 273) (codeMat 273) false
    det461 det273 inv273
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3968_lower : 17 ≤ frozenWangTable.L0 (spanCodes [131, 65, 32, 21]) := by
  have h := frozenWangTable.lower_le_L0 315 space3968_orbit
  simpa only [lower315] using h

theorem space3969_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [139, 73, 40, 29]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(139, 420), (73, 260), (40, 1), (29, 10)]
    (codeMat 330) (codeMat 468) (codeMat 87) false
    det330 det468 inv468
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3969_lower : 17 ≤ frozenWangTable.L0 (spanCodes [139, 73, 40, 29]) := by
  have h := frozenWangTable.lower_le_L0 315 space3969_orbit
  simpa only [lower315] using h

theorem space3970_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [136, 73, 43, 29]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(136, 420), (73, 260), (43, 11), (29, 10)]
    (codeMat 267) (codeMat 500) (codeMat 94) false
    det267 det500 inv500
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3970_lower : 17 ≤ frozenWangTable.L0 (spanCodes [136, 73, 43, 29]) := by
  have h := frozenWangTable.lower_le_L0 315 space3970_orbit
  simpa only [lower315] using h

theorem space3971_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [131, 67, 32, 23]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(131, 10), (67, 11), (32, 260), (23, 170)]
    (codeMat 396) (codeMat 281) (codeMat 281) false
    det396 det281 inv281
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3971_lower : 17 ≤ frozenWangTable.L0 (spanCodes [131, 67, 32, 23]) := by
  have h := frozenWangTable.lower_le_L0 315 space3971_orbit
  simpa only [lower315] using h

theorem space3972_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [140, 67, 47, 23]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(140, 171), (67, 420), (47, 10), (23, 11)]
    (codeMat 282) (codeMat 348) (codeMat 125) false
    det282 det348 inv348
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3972_lower : 17 ≤ frozenWangTable.L0 (spanCodes [140, 67, 47, 23]) := by
  have h := frozenWangTable.lower_le_L0 315 space3972_orbit
  simpa only [lower315] using h

theorem space3973_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [136, 64, 43, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(136, 11), (64, 1), (43, 170), (20, 430)]
    (codeMat 468) (codeMat 307) (codeMat 311) false
    det468 det307 inv307
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3973_lower : 17 ≤ frozenWangTable.L0 (spanCodes [136, 64, 43, 20]) := by
  have h := frozenWangTable.lower_le_L0 315 space3973_orbit
  simpa only [lower315] using h

theorem space3974_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [144, 84, 51, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(144, 1), (84, 421), (51, 170), (12, 430)]
    (codeMat 342) (codeMat 299) (codeMat 318) false
    det342 det299 inv299
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3974_lower : 17 ≤ frozenWangTable.L0 (spanCodes [144, 84, 51, 12]) := by
  have h := frozenWangTable.lower_le_L0 315 space3974_orbit
  simpa only [lower315] using h

theorem space3975_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [257, 163, 84, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(257, 160), (163, 270), (84, 171), (9, 260)]
    (codeMat 303) (codeMat 370) (codeMat 207) false
    det303 det370 inv370
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3975_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 163, 84, 9]) := by
  have h := frozenWangTable.lower_le_L0 315 space3975_orbit
  simpa only [lower315] using h

theorem space3976_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [272, 160, 84, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(272, 11), (160, 10), (84, 161), (3, 260)]
    (codeMat 486) (codeMat 123) (codeMat 236) false
    det486 det123 inv123
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3976_lower : 17 ≤ frozenWangTable.L0 (spanCodes [272, 160, 84, 3]) := by
  have h := frozenWangTable.lower_le_L0 315 space3976_orbit
  simpa only [lower315] using h

theorem space3977_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [257, 163, 64, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(257, 11), (163, 171), (64, 1), (20, 420)]
    (codeMat 236) (codeMat 177) (codeMat 417) false
    det236 det177 inv177
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3977_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 163, 64, 20]) := by
  have h := frozenWangTable.lower_le_L0 315 space3977_orbit
  simpa only [lower315] using h

theorem space3978_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [272, 163, 81, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(272, 420), (163, 161), (81, 430), (5, 1)]
    (codeMat 425) (codeMat 185) (codeMat 481) false
    det425 det185 inv185
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3978_lower : 17 ≤ frozenWangTable.L0 (spanCodes [272, 163, 81, 5]) := by
  have h := frozenWangTable.lower_le_L0 315 space3978_orbit
  simpa only [lower315] using h

theorem space3979_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [271, 142, 84, 45]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(271, 171), (142, 271), (84, 161), (45, 1)]
    (codeMat 379) (codeMat 494) (codeMat 501) false
    det379 det494 inv494
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3979_lower : 17 ≤ frozenWangTable.L0 (spanCodes [271, 142, 84, 45]) := by
  have h := frozenWangTable.lower_le_L0 315 space3979_orbit
  simpa only [lower315] using h

theorem space3980_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [273, 144, 84, 51]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(273, 171), (144, 1), (84, 431), (51, 160)]
    (codeMat 206) (codeMat 111) (codeMat 412) false
    det206 det111 inv111
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3980_lower : 17 ≤ frozenWangTable.L0 (spanCodes [273, 144, 84, 51]) := by
  have h := frozenWangTable.lower_le_L0 315 space3980_orbit
  simpa only [lower315] using h

theorem space3981_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [264, 136, 84, 43]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(264, 430), (136, 170), (84, 161), (43, 420)]
    (codeMat 247) (codeMat 247) (codeMat 379) false
    det247 det247 inv247
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3981_lower : 17 ≤ frozenWangTable.L0 (spanCodes [264, 136, 84, 43]) := by
  have h := frozenWangTable.lower_le_L0 315 space3981_orbit
  simpa only [lower315] using h

theorem space3982_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [273, 150, 84, 53]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(273, 161), (150, 11), (84, 421), (53, 160)]
    (codeMat 143) (codeMat 87) (codeMat 468) false
    det143 det87 inv87
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3982_lower : 17 ≤ frozenWangTable.L0 (spanCodes [273, 150, 84, 53]) := by
  have h := frozenWangTable.lower_le_L0 315 space3982_orbit
  simpa only [lower315] using h

theorem space3983_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 134, 84, 37]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 260), (134, 261), (84, 431), (37, 420)]
    (codeMat 125) (codeMat 394) (codeMat 330) false
    det125 det394 inv394
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3983_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 134, 84, 37]) := by
  have h := frozenWangTable.lower_le_L0 315 space3983_orbit
  simpa only [lower315] using h

theorem space3984_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [260, 128, 84, 35]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(260, 260), (128, 1), (84, 270), (35, 420)]
    (codeMat 116) (codeMat 331) (codeMat 410) false
    det116 det331 inv331
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3984_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 128, 84, 35]) := by
  have h := frozenWangTable.lower_le_L0 315 space3984_orbit
  simpa only [lower315] using h

theorem space3985_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [291, 163, 80, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(291, 10), (163, 270), (80, 170), (4, 1)]
    (codeMat 369) (codeMat 207) (codeMat 370) false
    det369 det207 inv207
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3985_lower : 17 ≤ frozenWangTable.L0 (spanCodes [291, 163, 80, 4]) := by
  have h := frozenWangTable.lower_le_L0 315 space3985_orbit
  simpa only [lower315] using h

theorem space3986_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [293, 161, 84, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(293, 170), (161, 431), (84, 421), (2, 260)]
    (codeMat 309) (codeMat 461) (codeMat 234) false
    det309 det461 inv461
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3986_lower : 17 ≤ frozenWangTable.L0 (spanCodes [293, 161, 84, 2]) := by
  have h := frozenWangTable.lower_le_L0 315 space3986_orbit
  simpa only [lower315] using h

theorem space3987_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [260, 139, 84, 40]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(260, 260), (139, 430), (84, 270), (40, 1)]
    (codeMat 498) (codeMat 339) (codeMat 467) false
    det498 det339 inv339
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3987_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 139, 84, 40]) := by
  have h := frozenWangTable.lower_le_L0 315 space3987_orbit
  simpa only [lower315] using h

theorem space3988_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [292, 163, 84, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(292, 1), (163, 161), (84, 431), (8, 260)]
    (codeMat 359) (codeMat 214) (codeMat 214) false
    det359 det214 inv214
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3988_lower : 17 ≤ frozenWangTable.L0 (spanCodes [292, 163, 84, 8]) := by
  have h := frozenWangTable.lower_le_L0 315 space3988_orbit
  simpa only [lower315] using h

theorem space3989_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [290, 163, 70, 18]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(290, 420), (163, 431), (70, 10), (18, 260)]
    (codeMat 421) (codeMat 425) (codeMat 249) false
    det421 det425 inv425
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3989_lower : 17 ≤ frozenWangTable.L0 (spanCodes [290, 163, 70, 18]) := by
  have h := frozenWangTable.lower_le_L0 315 space3989_orbit
  simpa only [lower315] using h

theorem space3990_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [257, 149, 84, 54]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(257, 430), (149, 420), (84, 270), (54, 1)]
    (codeMat 491) (codeMat 117) (codeMat 380) false
    det491 det117 inv117
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3990_lower : 17 ≤ frozenWangTable.L0 (spanCodes [257, 149, 84, 54]) := by
  have h := frozenWangTable.lower_le_L0 315 space3990_orbit
  simpa only [lower315] using h

theorem space3991_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [288, 163, 67, 23]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(288, 1), (163, 431), (67, 170), (23, 420)]
    (codeMat 174) (codeMat 93) (codeMat 372) false
    det174 det93 inv93
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3991_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 163, 67, 23]) := by
  have h := frozenWangTable.lower_le_L0 315 space3991_orbit
  simpa only [lower315] using h

theorem space3992_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [256, 155, 84, 56]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(256, 260), (155, 170), (84, 421), (56, 1)]
    (codeMat 442) (codeMat 410) (codeMat 331) false
    det442 det410 inv410
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3992_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 155, 84, 56]) := by
  have h := frozenWangTable.lower_le_L0 315 space3992_orbit
  simpa only [lower315] using h

theorem space3993_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [271, 148, 84, 55]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(271, 161), (148, 170), (84, 171), (55, 420)]
    (codeMat 188) (codeMat 478) (codeMat 445) false
    det188 det478 inv478
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3993_lower : 17 ≤ frozenWangTable.L0 (spanCodes [271, 148, 84, 55]) := by
  have h := frozenWangTable.lower_le_L0 315 space3993_orbit
  simpa only [lower315] using h

theorem space3994_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [288, 163, 76, 24]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(288, 1), (163, 421), (76, 10), (24, 260)]
    (codeMat 318) (codeMat 159) (codeMat 230) false
    det318 det159 inv159
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3994_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 163, 76, 24]) := by
  have h := frozenWangTable.lower_le_L0 315 space3994_orbit
  simpa only [lower315] using h

theorem space3995_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [275, 137, 84, 42]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(275, 271), (137, 430), (84, 171), (42, 160)]
    (codeMat 94) (codeMat 445) (codeMat 478) false
    det94 det445 inv445
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3995_lower : 17 ≤ frozenWangTable.L0 (spanCodes [275, 137, 84, 42]) := by
  have h := frozenWangTable.lower_le_L0 315 space3995_orbit
  simpa only [lower315] using h

theorem space3996_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [300, 163, 65, 21]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(300, 261), (163, 270), (65, 1), (21, 160)]
    (codeMat 157) (codeMat 405) (codeMat 407) false
    det157 det405 inv405
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3996_lower : 17 ≤ frozenWangTable.L0 (spanCodes [300, 163, 65, 21]) := by
  have h := frozenWangTable.lower_le_L0 315 space3996_orbit
  simpa only [lower315] using h

theorem space3997_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [272, 143, 84, 44]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(272, 170), (143, 271), (84, 270), (44, 160)]
    (codeMat 87) (codeMat 250) (codeMat 397) false
    det87 det250 inv250
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3997_lower : 17 ≤ frozenWangTable.L0 (spanCodes [272, 143, 84, 44]) := by
  have h := frozenWangTable.lower_le_L0 315 space3997_orbit
  simpa only [lower315] using h

theorem space3998_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [304, 163, 84, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(304, 170), (163, 421), (84, 270), (12, 160)]
    (codeMat 213) (codeMat 234) (codeMat 461) false
    det213 det234 inv234
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3998_lower : 17 ≤ frozenWangTable.L0 (spanCodes [304, 163, 84, 12]) := by
  have h := frozenWangTable.lower_le_L0 315 space3998_orbit
  simpa only [lower315] using h

theorem space3999_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [162, 80, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(162, 96), (80, 274), (4, 1), (1, 2)]
    (codeMat 169) (codeMat 140) (codeMat 98) false
    det169 det140 inv140
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3999_lower : 16 ≤ frozenWangTable.L0 (spanCodes [162, 80, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 276 space3999_orbit
  simpa only [lower276] using h


end QiushiMatmul.FrozenWang
