import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3904_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [257, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(257, 96), (163, 165), (84, 207)]
    (codeMat 124) (codeMat 394) (codeMat 330) true
    det124 det394 inv394
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3904_lower : 18 ≤ frozenWangTable.L0 (spanCodes [257, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3904_orbit
  simpa only [lower475] using h

theorem space3905_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [258, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(258, 10), (163, 169), (84, 84)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    det140 det98 inv98
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3905_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3905_orbit
  simpa only [lower467] using h

theorem space3906_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [259, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(259, 164), (163, 84), (84, 174)]
    (codeMat 307) (codeMat 379) (codeMat 247) false
    det307 det379 inv379
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3906_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3906_orbit
  simpa only [lower468] using h

theorem space3907_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [261, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(261, 293), (163, 303), (84, 379)]
    (codeMat 253) (codeMat 84) (codeMat 84) false
    det253 det84 inv84
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3907_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3907_orbit
  simpa only [lower473] using h

theorem space3908_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [262, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(262, 10), (163, 84), (84, 174)]
    (codeMat 233) (codeMat 85) (codeMat 340) false
    det233 det85 inv85
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3908_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3908_orbit
  simpa only [lower468] using h

theorem space3909_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [263, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(263, 96), (163, 372), (84, 286)]
    (codeMat 98) (codeMat 409) (codeMat 473) false
    det98 det409 inv409
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3909_lower : 18 ≤ frozenWangTable.L0 (spanCodes [263, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3909_orbit
  simpa only [lower476] using h

theorem space3910_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [265, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(265, 276), (163, 106), (84, 372)]
    (codeMat 190) (codeMat 442) (codeMat 334) false
    det190 det442 inv442
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3910_lower : 18 ≤ frozenWangTable.L0 (spanCodes [265, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3910_orbit
  simpa only [lower476] using h

theorem space3911_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [266, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(266, 84), (163, 303), (84, 369)]
    (codeMat 190) (codeMat 377) (codeMat 369) false
    det190 det377 inv377
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3911_lower : 18 ≤ frozenWangTable.L0 (spanCodes [266, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3911_orbit
  simpa only [lower473] using h

theorem space3912_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [267, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(267, 84), (163, 94), (84, 303)]
    (codeMat 214) (codeMat 473) (codeMat 409) false
    det214 det473 inv473
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3912_lower : 18 ≤ frozenWangTable.L0 (spanCodes [267, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3912_orbit
  simpa only [lower473] using h

theorem space3913_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [268, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(268, 10), (163, 84), (84, 174)]
    (codeMat 445) (codeMat 183) (codeMat 419) false
    det445 det183 inv183
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3913_lower : 18 ≤ frozenWangTable.L0 (spanCodes [268, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3913_orbit
  simpa only [lower468] using h

theorem space3914_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [269, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(269, 96), (163, 372), (84, 286)]
    (codeMat 382) (codeMat 354) (codeMat 142) true
    det382 det354 inv354
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3914_lower : 18 ≤ frozenWangTable.L0 (spanCodes [269, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3914_orbit
  simpa only [lower476] using h

theorem space3915_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [270, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(270, 369), (163, 84), (84, 303)]
    (codeMat 183) (codeMat 444) (codeMat 110) false
    det183 det444 inv444
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3915_lower : 18 ≤ frozenWangTable.L0 (spanCodes [270, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3915_orbit
  simpa only [lower473] using h

theorem space3916_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [272, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(272, 197), (163, 207), (84, 106)]
    (codeMat 190) (codeMat 477) (codeMat 431) false
    det190 det477 inv477
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3916_lower : 18 ≤ frozenWangTable.L0 (spanCodes [272, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3916_orbit
  simpa only [lower475] using h

theorem space3917_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [274, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(274, 10), (163, 286), (84, 106)]
    (codeMat 124) (codeMat 111) (codeMat 412) true
    det124 det111 inv111
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3917_lower : 18 ≤ frozenWangTable.L0 (spanCodes [274, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3917_orbit
  simpa only [lower476] using h

theorem space3918_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [278, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(278, 240), (163, 250), (84, 84)]
    (codeMat 375) (codeMat 477) (codeMat 431) false
    det375 det477 inv477
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3918_lower : 18 ≤ frozenWangTable.L0 (spanCodes [278, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3918_orbit
  simpa only [lower468] using h

theorem space3919_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [279, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(279, 94), (163, 174), (84, 250)]
    (codeMat 114) (codeMat 239) (codeMat 351) false
    det114 det239 inv239
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3919_lower : 18 ≤ frozenWangTable.L0 (spanCodes [279, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3919_orbit
  simpa only [lower468] using h

theorem space3920_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [280, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(280, 10), (163, 84), (84, 174)]
    (codeMat 340) (codeMat 226) (codeMat 141) false
    det340 det226 inv226
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3920_lower : 18 ≤ frozenWangTable.L0 (spanCodes [280, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3920_orbit
  simpa only [lower468] using h

theorem space3921_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [281, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(281, 169), (163, 247), (84, 163)]
    (codeMat 87) (codeMat 159) (codeMat 230) false
    det87 det159 inv159
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3921_lower : 18 ≤ frozenWangTable.L0 (spanCodes [281, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3921_orbit
  simpa only [lower467] using h

theorem space3922_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [282, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(282, 369), (163, 84), (84, 303)]
    (codeMat 123) (codeMat 369) (codeMat 377) false
    det123 det369 inv369
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3922_lower : 18 ≤ frozenWangTable.L0 (spanCodes [282, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3922_orbit
  simpa only [lower473] using h

theorem space3923_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [283, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(283, 293), (163, 303), (84, 379)]
    (codeMat 84) (codeMat 415) (codeMat 253) false
    det84 det415 inv415
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3923_lower : 18 ≤ frozenWangTable.L0 (spanCodes [283, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3923_orbit
  simpa only [lower473] using h

theorem space3924_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [284, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(284, 240), (163, 250), (84, 84)]
    (codeMat 187) (codeMat 442) (codeMat 334) false
    det187 det442 inv442
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3924_lower : 18 ≤ frozenWangTable.L0 (spanCodes [284, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3924_orbit
  simpa only [lower468] using h

theorem space3925_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [285, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(285, 94), (163, 174), (84, 250)]
    (codeMat 494) (codeMat 330) (codeMat 394) false
    det494 det330 inv330
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3925_lower : 18 ≤ frozenWangTable.L0 (spanCodes [285, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3925_orbit
  simpa only [lower468] using h

theorem space3926_orbit :
    frozenWangTable.OrbitImage 477 (spanCodes [286, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 477 [(286, 163), (163, 330), (84, 445)]
    (codeMat 87) (codeMat 117) (codeMat 380) false
    det87 det117 inv117
    (by rw [basis477]; decide +kernel)
    (by rw [basis477]; decide +kernel)

theorem space3926_lower : 18 ≤ frozenWangTable.L0 (spanCodes [286, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 477 space3926_orbit
  simpa only [lower477] using h

theorem space3927_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [287, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(287, 10), (163, 379), (84, 84)]
    (codeMat 110) (codeMat 236) (codeMat 123) false
    det110 det236 inv236
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3927_lower : 18 ≤ frozenWangTable.L0 (spanCodes [287, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3927_orbit
  simpa only [lower473] using h

theorem space3928_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [289, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(289, 240), (163, 250), (84, 84)]
    (codeMat 460) (codeMat 103) (codeMat 188) false
    det460 det103 inv103
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3928_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 468 space3928_orbit
  simpa only [lower468] using h

theorem space3929_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [290, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(290, 96), (163, 165), (84, 207)]
    (codeMat 117) (codeMat 330) (codeMat 394) false
    det117 det330 inv330
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3929_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3929_orbit
  simpa only [lower475] using h

theorem space3930_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [294, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(294, 293), (163, 303), (84, 379)]
    (codeMat 169) (codeMat 459) (codeMat 346) false
    det169 det459 inv459
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3930_lower : 18 ≤ frozenWangTable.L0 (spanCodes [294, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3930_orbit
  simpa only [lower473] using h

theorem space3931_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [295, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(295, 197), (163, 207), (84, 106)]
    (codeMat 172) (codeMat 93) (codeMat 372) true
    det172 det93 inv93
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3931_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 475 space3931_orbit
  simpa only [lower475] using h

theorem space3932_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [296, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(296, 10), (163, 369), (84, 94)]
    (codeMat 98) (codeMat 157) (codeMat 486) false
    det98 det157 inv157
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3932_lower : 18 ≤ frozenWangTable.L0 (spanCodes [296, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3932_orbit
  simpa only [lower473] using h

theorem space3933_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [297, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(297, 10), (163, 94), (84, 303)]
    (codeMat 117) (codeMat 174) (codeMat 359) false
    det117 det174 inv174
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3933_lower : 18 ≤ frozenWangTable.L0 (spanCodes [297, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 473 space3933_orbit
  simpa only [lower473] using h

theorem space3934_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [298, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(298, 247), (163, 253), (84, 169)]
    (codeMat 92) (codeMat 423) (codeMat 181) false
    det92 det423 inv423
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space3934_lower : 18 ≤ frozenWangTable.L0 (spanCodes [298, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 467 space3934_orbit
  simpa only [lower467] using h

theorem space3935_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [299, 163, 84]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(299, 382), (163, 372), (84, 286)]
    (codeMat 244) (codeMat 405) (codeMat 407) true
    det244 det405 inv405
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3935_lower : 18 ≤ frozenWangTable.L0 (spanCodes [299, 163, 84]) := by
  have h := frozenWangTable.lower_le_L0 476 space3935_orbit
  simpa only [lower476] using h


end QiushiMatmul.FrozenWang
