import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3936_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [300, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(300, 10), (163, 106), (84, 165)]
    (codeMat 239) (codeMat 183) (codeMat 419) false
    det239 det183 inv183
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3936_lower : 18 ≤ frozenWangTable.L0 (spanCodes [300, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3936_orbit
  simpa only [lower475] using h

theorem space3937_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [301, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(301, 10), (163, 303), (84, 369)]
    (codeMat 95) (codeMat 179) (codeMat 421) false
    det95 det179 inv179
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3937_lower : 18 ≤ frozenWangTable.L0 (spanCodes [301, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3937_orbit
  simpa only [lower473] using h

theorem space3938_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [302, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(302, 84), (163, 163), (84, 94)]
    (codeMat 93) (codeMat 346) (codeMat 459) false
    det93 det346 inv346
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3938_lower : 18 ≤ frozenWangTable.L0 (spanCodes [302, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3938_orbit
  simpa only [lower467] using h

theorem space3939_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [303, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(303, 163), (163, 94), (84, 247)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    det84 det253 inv253
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3939_lower : 18 ≤ frozenWangTable.L0 (spanCodes [303, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3939_orbit
  simpa only [lower467] using h

theorem space3940_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [305, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(305, 94), (163, 250), (84, 84)]
    (codeMat 298) (codeMat 169) (codeMat 225) false
    det298 det169 inv169
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3940_lower : 18 ≤ frozenWangTable.L0 (spanCodes [305, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3940_orbit
  simpa only [lower468] using h

theorem space3941_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [306, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(306, 293), (163, 369), (84, 94)]
    (codeMat 141) (codeMat 334) (codeMat 442) false
    det141 det334 inv334
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3941_lower : 18 ≤ frozenWangTable.L0 (spanCodes [306, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3941_orbit
  simpa only [lower473] using h

theorem space3942_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [307, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(307, 369), (163, 84), (84, 303)]
    (codeMat 204) (codeMat 205) (codeMat 242) false
    det204 det205 inv205
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3942_lower : 18 ≤ frozenWangTable.L0 (spanCodes [307, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3942_orbit
  simpa only [lower473] using h

theorem space3943_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [308, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(308, 276), (163, 106), (84, 372)]
    (codeMat 172) (codeMat 250) (codeMat 397) true
    det172 det250 inv250
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3943_lower : 18 ≤ frozenWangTable.L0 (spanCodes [308, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3943_orbit
  simpa only [lower476] using h

theorem space3944_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [309, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(309, 382), (163, 372), (84, 286)]
    (codeMat 239) (codeMat 85) (codeMat 340) false
    det239 det85 inv85
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3944_lower : 18 ≤ frozenWangTable.L0 (spanCodes [309, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3944_orbit
  simpa only [lower476] using h

theorem space3945_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [310, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(310, 10), (163, 379), (84, 84)]
    (codeMat 156) (codeMat 114) (codeMat 204) false
    det156 det114 inv114
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3945_lower : 18 ≤ frozenWangTable.L0 (spanCodes [310, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3945_orbit
  simpa only [lower473] using h

theorem space3946_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [312, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(312, 10), (163, 207), (84, 106)]
    (codeMat 86) (codeMat 250) (codeMat 397) true
    det86 det250 inv250
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3946_lower : 18 ≤ frozenWangTable.L0 (spanCodes [312, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3946_orbit
  simpa only [lower475] using h

theorem space3947_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [314, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(314, 247), (163, 94), (84, 253)]
    (codeMat 142) (codeMat 501) (codeMat 494) false
    det142 det501 inv501
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3947_lower : 18 ≤ frozenWangTable.L0 (spanCodes [314, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3947_orbit
  simpa only [lower467] using h

theorem space3948_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [315, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(315, 10), (163, 286), (84, 106)]
    (codeMat 117) (codeMat 239) (codeMat 351) false
    det117 det239 inv239
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3948_lower : 18 ≤ frozenWangTable.L0 (spanCodes [315, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3948_orbit
  simpa only [lower476] using h

theorem space3949_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [317, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(317, 379), (163, 369), (84, 94)]
    (codeMat 239) (codeMat 467) (codeMat 339) false
    det239 det467 inv467
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3949_lower : 18 ≤ frozenWangTable.L0 (spanCodes [317, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3949_orbit
  simpa only [lower473] using h

theorem space3950_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [318, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(318, 94), (163, 174), (84, 250)]
    (codeMat 412) (codeMat 421) (codeMat 179) false
    det412 det421 inv421
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3950_lower : 18 ≤ frozenWangTable.L0 (spanCodes [318, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3950_orbit
  simpa only [lower468] using h

theorem space3951_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [319, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(319, 240), (163, 174), (84, 250)]
    (codeMat 313) (codeMat 470) (codeMat 213) false
    det313 det470 inv470
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3951_lower : 18 ≤ frozenWangTable.L0 (spanCodes [319, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3951_orbit
  simpa only [lower468] using h

theorem space3952_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [160, 68, 16, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(160, 10), (68, 170), (16, 1), (3, 260)]
    (codeMat 226) (codeMat 99) (codeMat 172) false
    det226 det99 inv99
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3952_lower : 17 ≤ frozenWangTable.L0 (spanCodes [160, 68, 16, 3]) := by
  have h := frozenWangTable.lower_le_L0 315 space3952_orbit
  simpa only [lower315] using h

theorem space3953_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [162, 70, 18, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(162, 420), (70, 10), (18, 260), (1, 1)]
    (codeMat 161) (codeMat 417) (codeMat 177) false
    det161 det417 inv417
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3953_lower : 17 ≤ frozenWangTable.L0 (spanCodes [162, 70, 18, 1]) := by
  have h := frozenWangTable.lower_le_L0 315 space3953_orbit
  simpa only [lower315] using h

theorem space3954_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [163, 68, 16, 9]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(163, 270), (68, 160), (16, 1), (9, 260)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    det106 det354 inv354
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3954_lower : 17 ≤ frozenWangTable.L0 (spanCodes [163, 68, 16, 9]) := by
  have h := frozenWangTable.lower_le_L0 315 space3954_orbit
  simpa only [lower315] using h

theorem space3955_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [162, 76, 24, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(162, 430), (76, 10), (24, 260), (1, 1)]
    (codeMat 249) (codeMat 167) (codeMat 167) false
    det249 det167 inv167
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3955_lower : 17 ≤ frozenWangTable.L0 (spanCodes [162, 76, 24, 1]) := by
  have h := frozenWangTable.lower_le_L0 315 space3955_orbit
  simpa only [lower315] using h

theorem space3956_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [163, 71, 19, 8]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(163, 171), (71, 160), (19, 261), (8, 260)]
    (codeMat 99) (codeMat 230) (codeMat 159) false
    det99 det230 inv230
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3956_lower : 17 ≤ frozenWangTable.L0 (spanCodes [163, 71, 19, 8]) := by
  have h := frozenWangTable.lower_le_L0 315 space3956_orbit
  simpa only [lower315] using h

theorem space3957_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [161, 77, 25, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(161, 421), (77, 170), (25, 261), (2, 260)]
    (codeMat 179) (codeMat 485) (codeMat 171) false
    det179 det485 inv485
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3957_lower : 17 ≤ frozenWangTable.L0 (spanCodes [161, 77, 25, 2]) := by
  have h := frozenWangTable.lower_le_L0 315 space3957_orbit
  simpa only [lower315] using h

theorem space3958_orbit :
    frozenWangTable.OrbitImage 449 (spanCodes [135, 84, 36]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 449 [(135, 160), (84, 412), (36, 1)]
    (codeMat 107) (codeMat 141) (codeMat 226) false
    det107 det141 inv141
    (by rw [basis449]; decide +kernel)
    (by rw [basis449]; decide +kernel)

theorem space3958_lower : 17 ≤ frozenWangTable.L0 (spanCodes [135, 84, 36]) := by
  have h := frozenWangTable.lower_le_L0 449 space3958_orbit
  simpa only [lower449] using h

theorem space3959_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [130, 80, 33, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(130, 260), (80, 160), (33, 10), (4, 1)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    det273 det140 inv140
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3959_lower : 17 ≤ frozenWangTable.L0 (spanCodes [130, 80, 33, 4]) := by
  have h := frozenWangTable.lower_le_L0 315 space3959_orbit
  simpa only [lower315] using h

theorem space3960_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [128, 82, 35, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(128, 1), (82, 10), (35, 430), (6, 260)]
    (codeMat 348) (codeMat 270) (codeMat 298) false
    det348 det270 inv270
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3960_lower : 17 ≤ frozenWangTable.L0 (spanCodes [128, 82, 35, 6]) := by
  have h := frozenWangTable.lower_le_L0 315 space3960_orbit
  simpa only [lower315] using h

theorem space3961_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [137, 82, 42, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(137, 11), (82, 10), (42, 430), (6, 260)]
    (codeMat 415) (codeMat 318) (codeMat 299) false
    det415 det318 inv318
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3961_lower : 17 ≤ frozenWangTable.L0 (spanCodes [137, 82, 42, 6]) := by
  have h := frozenWangTable.lower_le_L0 315 space3961_orbit
  simpa only [lower315] using h

theorem space3962_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [130, 84, 33, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(130, 260), (84, 171), (33, 10), (12, 11)]
    (codeMat 403) (codeMat 172) (codeMat 99) false
    det403 det172 inv172
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3962_lower : 17 ≤ frozenWangTable.L0 (spanCodes [130, 84, 33, 12]) := by
  have h := frozenWangTable.lower_le_L0 315 space3962_orbit
  simpa only [lower315] using h

theorem space3963_orbit :
    frozenWangTable.OrbitImage 315 (spanCodes [137, 81, 42, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 315 [(137, 160), (81, 420), (42, 11), (5, 1)]
    (codeMat 473) (codeMat 380) (codeMat 117) false
    det473 det380 inv380
    (by rw [basis315]; decide +kernel)
    (by rw [basis315]; decide +kernel)

theorem space3963_lower : 17 ≤ frozenWangTable.L0 (spanCodes [137, 81, 42, 5]) := by
  have h := frozenWangTable.lower_le_L0 315 space3963_orbit
  simpa only [lower315] using h

theorem space3964_orbit :
    frozenWangTable.OrbitImage 449 (spanCodes [147, 84, 48]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 449 [(147, 316), (84, 161), (48, 1)]
    (codeMat 250) (codeMat 498) (codeMat 206) false
    det250 det498 inv498
    (by rw [basis449]; decide +kernel)
    (by rw [basis449]; decide +kernel)

theorem space3964_lower : 17 ≤ frozenWangTable.L0 (spanCodes [147, 84, 48]) := by
  have h := frozenWangTable.lower_le_L0 449 space3964_orbit
  simpa only [lower449] using h

theorem space3965_orbit :
    frozenWangTable.OrbitImage 322 (spanCodes [133, 66, 38, 22]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 322 [(133, 170), (66, 308), (38, 11), (22, 10)]
    (codeMat 458) (codeMat 116) (codeMat 92) false
    det458 det116 inv116
    (by rw [basis322]; decide +kernel)
    (by rw [basis322]; decide +kernel)

theorem space3965_lower : 17 ≤ frozenWangTable.L0 (spanCodes [133, 66, 38, 22]) := by
  have h := frozenWangTable.lower_le_L0 322 space3965_orbit
  simpa only [lower322] using h

theorem space3966_orbit :
    frozenWangTable.OrbitImage 449 (spanCodes [146, 84, 49]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 449 [(146, 1), (84, 412), (49, 160)]
    (codeMat 159) (codeMat 358) (codeMat 158) false
    det159 det358 inv358
    (by rw [basis449]; decide +kernel)
    (by rw [basis449]; decide +kernel)

theorem space3966_lower : 17 ≤ frozenWangTable.L0 (spanCodes [146, 84, 49]) := by
  have h := frozenWangTable.lower_le_L0 449 space3966_orbit
  simpa only [lower449] using h

theorem space3967_orbit :
    frozenWangTable.OrbitImage 449 (spanCodes [151, 84, 52]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 449 [(151, 316), (84, 317), (52, 160)]
    (codeMat 205) (codeMat 481) (codeMat 185) false
    det205 det481 inv481
    (by rw [basis449]; decide +kernel)
    (by rw [basis449]; decide +kernel)

theorem space3967_lower : 17 ≤ frozenWangTable.L0 (spanCodes [151, 84, 52]) := by
  have h := frozenWangTable.lower_le_L0 449 space3967_orbit
  simpa only [lower449] using h


end QiushiMatmul.FrozenWang
