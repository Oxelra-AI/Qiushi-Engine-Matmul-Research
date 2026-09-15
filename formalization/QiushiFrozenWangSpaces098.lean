import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3136_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [258, 98, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(258, 257), (98, 267), (10, 280)]
    (codeMat 84) (codeMat 141) (codeMat 226) false
    det84 det141 inv141
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space3136_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 98, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space3136_orbit
  simpa only [lower451] using h

theorem space3137_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 99, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 450), (99, 470), (10, 476)]
    (codeMat 239) (codeMat 143) (codeMat 482) true
    det239 det143 inv143
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3137_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 99, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3137_orbit
  simpa only [lower458] using h

theorem space3138_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 100, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 126), (100, 20), (10, 96)]
    (codeMat 249) (codeMat 188) (codeMat 103) true
    det249 det188 inv188
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3138_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 100, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3138_orbit
  simpa only [lower454] using h

theorem space3139_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 102, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 456), (102, 470), (10, 476)]
    (codeMat 181) (codeMat 185) (codeMat 481) true
    det181 det185 inv185
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3139_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 102, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3139_orbit
  simpa only [lower458] using h

theorem space3140_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 103, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 469), (103, 459), (10, 479)]
    (codeMat 230) (codeMat 174) (codeMat 359) true
    det230 det174 inv174
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3140_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 103, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3140_orbit
  simpa only [lower457] using h

theorem space3141_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 112, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 96), (112, 20), (10, 126)]
    (codeMat 358) (codeMat 334) (codeMat 442) false
    det358 det334 inv334
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3141_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 112, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3141_orbit
  simpa only [lower454] using h

theorem space3142_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [258, 113, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(258, 68), (113, 78), (10, 240)]
    (codeMat 93) (codeMat 458) (codeMat 458) false
    det93 det458 inv458
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space3142_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 113, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space3142_orbit
  simpa only [lower464] using h

theorem space3143_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 114, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 456), (114, 470), (10, 450)]
    (codeMat 98) (codeMat 158) (codeMat 358) false
    det98 det158 inv158
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3143_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 114, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3143_orbit
  simpa only [lower458] using h

theorem space3144_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [258, 115, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(258, 10), (115, 94), (10, 383)]
    (codeMat 229) (codeMat 117) (codeMat 380) false
    det229 det117 inv117
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3144_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 115, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3144_orbit
  simpa only [lower471] using h

theorem space3145_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 116, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 265), (116, 94), (10, 259)]
    (codeMat 114) (codeMat 141) (codeMat 226) false
    det114 det141 inv141
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3145_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 116, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3145_orbit
  simpa only [lower470] using h

theorem space3146_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 117, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 10), (117, 84), (10, 349)]
    (codeMat 461) (codeMat 115) (codeMat 492) false
    det461 det115 inv115
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3146_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 117, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3146_orbit
  simpa only [lower470] using h

theorem space3147_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 118, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 300), (118, 376), (10, 294)]
    (codeMat 482) (codeMat 140) (codeMat 98) false
    det482 det140 inv140
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3147_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 118, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3147_orbit
  simpa only [lower474] using h

theorem space3148_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 119, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 68), (119, 78), (10, 383)]
    (codeMat 125) (codeMat 459) (codeMat 346) false
    det125 det459 inv459
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3148_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 119, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3148_orbit
  simpa only [lower466] using h

theorem space3149_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 128, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 10), (128, 1), (10, 264)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    det140 det98 inv98
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3149_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 128, 10]) := by
  have h := frozenWangTable.lower_le_L0 425 space3149_orbit
  simpa only [lower425] using h

theorem space3150_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 129, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 20), (129, 10), (10, 80)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    det140 det273 inv273
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3150_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 129, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3150_orbit
  simpa only [lower453] using h

theorem space3151_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 131, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 30), (131, 10), (10, 139)]
    (codeMat 492) (codeMat 286) (codeMat 303) false
    det492 det286 inv286
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3151_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 131, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3151_orbit
  simpa only [lower455] using h

theorem space3152_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [258, 132, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(258, 11), (132, 10), (10, 272)]
    (codeMat 141) (codeMat 116) (codeMat 92) false
    det141 det116 inv116
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space3152_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 132, 10]) := by
  have h := frozenWangTable.lower_le_L0 426 space3152_orbit
  simpa only [lower426] using h

theorem space3153_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 133, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 30), (133, 20), (10, 126)]
    (codeMat 421) (codeMat 405) (codeMat 407) false
    det421 det405 inv405
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3153_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 133, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3153_orbit
  simpa only [lower454] using h

theorem space3154_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [258, 134, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(258, 25), (134, 19), (10, 280)]
    (codeMat 140) (codeMat 86) (codeMat 212) false
    det140 det86 inv86
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space3154_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 134, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space3154_orbit
  simpa only [lower451] using h

theorem space3155_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 135, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 10), (135, 20), (10, 450)]
    (codeMat 161) (codeMat 93) (codeMat 372) false
    det161 det93 inv93
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3155_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 135, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3155_orbit
  simpa only [lower458] using h

theorem space3156_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 145, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 126), (145, 20), (10, 30)]
    (codeMat 444) (codeMat 314) (codeMat 271) true
    det444 det314 inv314
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3156_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 145, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3156_orbit
  simpa only [lower454] using h

theorem space3157_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 147, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 456), (147, 30), (10, 20)]
    (codeMat 157) (codeMat 313) (codeMat 313) true
    det157 det313 inv313
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3157_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 147, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3157_orbit
  simpa only [lower458] using h

theorem space3158_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 148, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 30), (148, 20), (10, 126)]
    (codeMat 442) (codeMat 122) (codeMat 460) true
    det442 det122 inv122
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3158_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 148, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3158_orbit
  simpa only [lower454] using h

theorem space3159_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [258, 149, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(258, 180), (149, 78), (10, 240)]
    (codeMat 158) (codeMat 465) (codeMat 465) false
    det158 det465 inv465
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space3159_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 149, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space3159_orbit
  simpa only [lower464] using h

theorem space3160_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 150, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 30), (150, 10), (10, 476)]
    (codeMat 247) (codeMat 87) (codeMat 468) true
    det247 det87 inv87
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3160_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 150, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3160_orbit
  simpa only [lower458] using h

theorem space3161_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [258, 151, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(258, 373), (151, 289), (10, 383)]
    (codeMat 230) (codeMat 174) (codeMat 359) false
    det230 det174 inv174
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3161_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 151, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3161_orbit
  simpa only [lower471] using h

theorem space3162_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 160, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 80), (160, 10), (10, 68)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    det98 det98 inv98
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3162_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 160, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3162_orbit
  simpa only [lower453] using h

theorem space3163_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [258, 161, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(258, 258), (161, 84), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    det84 det161 inv161
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space3163_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 161, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space3163_orbit
  simpa only [lower469] using h

theorem space3164_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 162, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 139), (162, 129), (10, 149)]
    (codeMat 498) (codeMat 117) (codeMat 380) false
    det498 det117 inv117
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3164_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 162, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3164_orbit
  simpa only [lower455] using h

theorem space3165_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [258, 163, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(258, 290), (163, 380), (10, 296)]
    (codeMat 212) (codeMat 161) (codeMat 161) false
    det212 det161 inv161
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space3165_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 163, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space3165_orbit
  simpa only [lower472] using h

theorem space3166_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 164, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 30), (164, 20), (10, 96)]
    (codeMat 250) (codeMat 124) (codeMat 124) true
    det250 det124 inv124
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3166_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 164, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3166_orbit
  simpa only [lower454] using h

theorem space3167_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 165, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 10), (165, 94), (10, 259)]
    (codeMat 169) (codeMat 86) (codeMat 212) false
    det169 det86 inv86
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3167_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 165, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3167_orbit
  simpa only [lower470] using h


end QiushiMatmul.FrozenWang
