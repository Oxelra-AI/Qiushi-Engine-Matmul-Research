import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3104_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [272, 130, 66, 34, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(272, 70), (130, 511), (66, 186), (34, 440), (10, 184), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 442) (codeMat 334) false
    det142 det442 inv442
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3104_lower : 12 ≤ frozenWangTable.L0 (spanCodes [272, 130, 66, 34, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3104_orbit
  simpa only [lower10] using h

theorem space3105_orbit :
    frozenWangTable.OrbitImage 10 (spanCodes [274, 128, 66, 34, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 10 [(274, 238), (128, 325), (66, 170), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 426) (codeMat 335) false
    det142 det426 inv426
    (by rw [basis10]; decide +kernel)
    (by rw [basis10]; decide +kernel)

theorem space3105_lower : 12 ≤ frozenWangTable.L0 (spanCodes [274, 128, 66, 34, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 10 space3105_orbit
  simpa only [lower10] using h

theorem space3106_orbit :
    frozenWangTable.OrbitImage 11 (spanCodes [256, 144, 66, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 11 [(256, 216), (144, 32), (66, 76), (34, 196), (10, 68), (4, 3), (1, 1)]
    (codeMat 177) (codeMat 165) (codeMat 163) false
    det177 det165 inv165
    (by rw [basis11]; decide +kernel)
    (by rw [basis11]; decide +kernel)

theorem space3106_lower : 12 ≤ frozenWangTable.L0 (spanCodes [256, 144, 66, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 11 space3106_orbit
  simpa only [lower11] using h

theorem space3107_orbit :
    frozenWangTable.OrbitImage 7 (spanCodes [259, 131, 64, 32, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 7 [(259, 30), (131, 374), (64, 365), (32, 16), (18, 256), (10, 274), (7, 6)]
    (codeMat 215) (codeMat 233) (codeMat 233) true
    det215 det233 inv233
    (by rw [basis7]; decide +kernel)
    (by rw [basis7]; decide +kernel)

theorem space3107_lower : 9 ≤ frozenWangTable.L0 (spanCodes [259, 131, 64, 32, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 7 space3107_orbit
  simpa only [lower7] using h

theorem space3108_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 327), (129, 324), (65, 325), (33, 376), (16, 32), (8, 40), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 485) (codeMat 171) false
    det84 det485 inv485
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3108_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space3108_orbit
  simpa only [lower3] using h

theorem space3109_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 33, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (128, 3), (65, 455), (33, 464), (17, 472), (9, 504), (4, 128), (3, 256)]
    (codeMat 84) (codeMat 123) (codeMat 236) false
    det84 det123 inv123
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3109_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 33, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space3109_orbit
  simpa only [lower3] using h

theorem space3110_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 258), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3110_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 425 space3110_orbit
  simpa only [lower425] using h

theorem space3111_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 10), (10, 258), (4, 1)]
    (codeMat 161) (codeMat 84) (codeMat 84) false
    det161 det84 inv84
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3111_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 425 space3111_orbit
  simpa only [lower425] using h

theorem space3112_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 264), (16, 1), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3112_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 425 space3112_orbit
  simpa only [lower425] using h

theorem space3113_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [258, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(258, 272), (17, 10), (10, 11)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    det267 det281 inv281
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space3113_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 426 space3113_orbit
  simpa only [lower426] using h

theorem space3114_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 126), (21, 20), (10, 30)]
    (codeMat 403) (codeMat 213) (codeMat 470) false
    det403 det213 inv213
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3114_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3114_orbit
  simpa only [lower454] using h

theorem space3115_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 139), (22, 10), (10, 30)]
    (codeMat 474) (codeMat 115) (codeMat 492) false
    det474 det115 inv115
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3115_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3115_orbit
  simpa only [lower455] using h

theorem space3116_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 450), (23, 20), (10, 10)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    det273 det309 inv309
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3116_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3116_orbit
  simpa only [lower458] using h

theorem space3117_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 32, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 264), (32, 1), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    det98 det140 inv140
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3117_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 32, 10]) := by
  have h := frozenWangTable.lower_le_L0 425 space3117_orbit
  simpa only [lower425] using h

theorem space3118_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 68), (33, 10), (10, 20)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    det273 det140 inv140
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3118_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3118_orbit
  simpa only [lower453] using h

theorem space3119_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 35, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 149), (35, 20), (10, 30)]
    (codeMat 473) (codeMat 171) (codeMat 485) false
    det473 det171 inv171
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3119_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 35, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3119_orbit
  simpa only [lower455] using h

theorem space3120_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 37, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 78), (37, 10), (10, 30)]
    (codeMat 401) (codeMat 157) (codeMat 486) false
    det401 det157 inv157
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3120_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 37, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3120_orbit
  simpa only [lower453] using h

theorem space3121_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 96), (49, 20), (10, 30)]
    (codeMat 331) (codeMat 206) (codeMat 498) false
    det331 det206 inv206
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3121_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3121_orbit
  simpa only [lower454] using h

theorem space3122_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 456), (51, 30), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3122_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3122_orbit
  simpa only [lower458] using h

theorem space3123_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 52, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 80), (52, 10), (10, 30)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    det330 det94 inv94
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3123_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 52, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3123_orbit
  simpa only [lower453] using h

theorem space3124_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 449), (55, 10), (10, 30)]
    (codeMat 337) (codeMat 445) (codeMat 478) false
    det337 det445 inv445
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3124_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3124_orbit
  simpa only [lower457] using h

theorem space3125_orbit :
    frozenWangTable.OrbitImage 425 (spanCodes [258, 64, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 425 [(258, 258), (64, 1), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    det84 det161 inv161
    (by rw [basis425]; decide +kernel)
    (by rw [basis425]; decide +kernel)

theorem space3125_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 64, 10]) := by
  have h := frozenWangTable.lower_le_L0 425 space3125_orbit
  simpa only [lower425] using h

theorem space3126_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 69, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 30), (69, 10), (10, 78)]
    (codeMat 417) (codeMat 181) (codeMat 423) false
    det417 det181 inv181
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3126_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 69, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3126_orbit
  simpa only [lower453] using h

theorem space3127_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 70, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 30), (70, 20), (10, 149)]
    (codeMat 489) (codeMat 174) (codeMat 359) false
    det489 det174 inv174
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3127_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 70, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3127_orbit
  simpa only [lower455] using h

theorem space3128_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 80, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 68), (80, 10), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    det84 det266 inv266
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3128_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 80, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3128_orbit
  simpa only [lower453] using h

theorem space3129_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 81, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 96), (81, 20), (10, 30)]
    (codeMat 380) (codeMat 313) (codeMat 313) true
    det380 det313 inv313
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3129_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 81, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3129_orbit
  simpa only [lower454] using h

theorem space3130_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [258, 82, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(258, 149), (82, 129), (10, 139)]
    (codeMat 500) (codeMat 285) (codeMat 317) false
    det500 det285 inv285
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space3130_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 82, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space3130_orbit
  simpa only [lower455] using h

theorem space3131_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 83, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 476), (83, 10), (10, 20)]
    (codeMat 94) (codeMat 314) (codeMat 271) true
    det94 det314 inv314
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3131_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 83, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3131_orbit
  simpa only [lower458] using h

theorem space3132_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 85, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 259), (85, 94), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    det281 det275 inv275
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3132_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 85, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3132_orbit
  simpa only [lower470] using h

theorem space3133_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [258, 86, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(258, 10), (86, 84), (10, 296)]
    (codeMat 204) (codeMat 98) (codeMat 140) false
    det204 det98 inv98
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space3133_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 86, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space3133_orbit
  simpa only [lower472] using h

theorem space3134_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 87, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 294), (87, 94), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    det465 det273 inv273
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3134_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 87, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3134_orbit
  simpa only [lower474] using h

theorem space3135_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 97, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 96), (97, 20), (10, 126)]
    (codeMat 377) (codeMat 185) (codeMat 481) true
    det377 det185 inv185
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3135_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 97, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3135_orbit
  simpa only [lower454] using h


end QiushiMatmul.FrozenWang
