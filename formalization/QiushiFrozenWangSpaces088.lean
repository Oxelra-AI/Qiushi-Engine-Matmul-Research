import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2816_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [164, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(164, 10), (96, 78), (10, 304)]
    (codeMat 92) (codeMat 92) (codeMat 116) false
    det92 det92 inv92
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2816_lower : 18 ≤ frozenWangTable.L0 (spanCodes [164, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2816_orbit
  simpa only [lower465] using h

theorem space2817_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [165, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(165, 165), (96, 96), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2817_lower : 18 ≤ frozenWangTable.L0 (spanCodes [165, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2817_orbit
  simpa only [lower475] using h

theorem space2818_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [166, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(166, 10), (96, 290), (10, 374)]
    (codeMat 110) (codeMat 122) (codeMat 460) false
    det110 det122 inv122
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2818_lower : 18 ≤ frozenWangTable.L0 (spanCodes [166, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2818_orbit
  simpa only [lower472] using h

theorem space2819_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [167, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(167, 165), (96, 197), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) true
    det345 det275 inv275
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2819_lower : 18 ≤ frozenWangTable.L0 (spanCodes [167, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2819_orbit
  simpa only [lower475] using h

theorem space2820_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [176, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(176, 20), (96, 30), (10, 129)]
    (codeMat 226) (codeMat 313) (codeMat 313) false
    det226 det313 inv313
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2820_lower : 18 ≤ frozenWangTable.L0 (spanCodes [176, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2820_orbit
  simpa only [lower455] using h

theorem space2821_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [179, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(179, 181), (96, 191), (10, 20)]
    (codeMat 213) (codeMat 267) (codeMat 282) true
    det213 det267 inv267
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2821_lower : 18 ≤ frozenWangTable.L0 (spanCodes [179, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2821_orbit
  simpa only [lower456] using h

theorem space2822_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [180, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(180, 197), (96, 96), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    det266 det266 inv266
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2822_lower : 18 ≤ frozenWangTable.L0 (spanCodes [180, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2822_orbit
  simpa only [lower475] using h

theorem space2823_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [181, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(181, 380), (96, 290), (10, 374)]
    (codeMat 124) (codeMat 346) (codeMat 459) false
    det124 det346 inv346
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2823_lower : 18 ≤ frozenWangTable.L0 (spanCodes [181, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2823_orbit
  simpa only [lower472] using h

theorem space2824_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [182, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(182, 96), (96, 197), (10, 10)]
    (codeMat 282) (codeMat 271) (codeMat 314) false
    det282 det271 inv271
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2824_lower : 18 ≤ frozenWangTable.L0 (spanCodes [182, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2824_orbit
  simpa only [lower475] using h

theorem space2825_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [183, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(183, 314), (96, 78), (10, 304)]
    (codeMat 94) (codeMat 380) (codeMat 117) false
    det94 det380 inv380
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2825_lower : 18 ≤ frozenWangTable.L0 (spanCodes [183, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2825_orbit
  simpa only [lower465] using h

theorem space2826_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [256, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(256, 1), (96, 10), (10, 272)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    det84 det140 inv140
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space2826_lower : 18 ≤ frozenWangTable.L0 (spanCodes [256, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 426 space2826_orbit
  simpa only [lower426] using h

theorem space2827_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [257, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(257, 10), (96, 20), (10, 96)]
    (codeMat 161) (codeMat 140) (codeMat 98) true
    det161 det140 inv140
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2827_lower : 18 ≤ frozenWangTable.L0 (spanCodes [257, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2827_orbit
  simpa only [lower454] using h

theorem space2828_orbit :
    frozenWangTable.OrbitImage 426 (spanCodes [258, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 426 [(258, 283), (96, 10), (10, 272)]
    (codeMat 86) (codeMat 172) (codeMat 99) false
    det86 det172 inv172
    (by rw [basis426]; decide +kernel)
    (by rw [basis426]; decide +kernel)

theorem space2828_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 426 space2828_orbit
  simpa only [lower426] using h

theorem space2829_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [259, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(259, 126), (96, 20), (10, 96)]
    (codeMat 177) (codeMat 172) (codeMat 99) true
    det177 det172 inv172
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2829_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2829_orbit
  simpa only [lower454] using h

theorem space2830_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [261, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(261, 10), (96, 20), (10, 126)]
    (codeMat 417) (codeMat 157) (codeMat 486) true
    det417 det157 inv157
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2830_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2830_orbit
  simpa only [lower454] using h

theorem space2831_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [262, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(262, 96), (96, 20), (10, 126)]
    (codeMat 305) (codeMat 185) (codeMat 481) true
    det305 det185 inv185
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2831_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2831_orbit
  simpa only [lower454] using h

theorem space2832_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [272, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(272, 10), (96, 20), (10, 96)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    det84 det98 inv98
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2832_lower : 18 ≤ frozenWangTable.L0 (spanCodes [272, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2832_orbit
  simpa only [lower454] using h

theorem space2833_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [273, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(273, 174), (96, 240), (10, 164)]
    (codeMat 167) (codeMat 236) (codeMat 123) false
    det167 det236 inv236
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2833_lower : 18 ≤ frozenWangTable.L0 (spanCodes [273, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2833_orbit
  simpa only [lower468] using h

theorem space2834_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [274, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(274, 126), (96, 20), (10, 96)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    det86 det354 inv354
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2834_lower : 18 ≤ frozenWangTable.L0 (spanCodes [274, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2834_orbit
  simpa only [lower454] using h

theorem space2835_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [275, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(275, 250), (96, 240), (10, 164)]
    (codeMat 181) (codeMat 460) (codeMat 122) false
    det181 det460 inv460
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2835_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2835_orbit
  simpa only [lower468] using h

theorem space2836_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [276, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(276, 10), (96, 276), (10, 96)]
    (codeMat 85) (codeMat 98) (codeMat 140) false
    det85 det98 inv98
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space2836_lower : 18 ≤ frozenWangTable.L0 (spanCodes [276, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space2836_orbit
  simpa only [lower476] using h

theorem space2837_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [277, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(277, 94), (96, 259), (10, 343)]
    (codeMat 444) (codeMat 345) (codeMat 345) false
    det444 det345 inv345
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2837_lower : 18 ≤ frozenWangTable.L0 (spanCodes [277, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2837_orbit
  simpa only [lower470] using h

theorem space2838_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [278, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(278, 10), (96, 259), (10, 343)]
    (codeMat 302) (codeMat 125) (codeMat 348) false
    det302 det125 inv125
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2838_lower : 18 ≤ frozenWangTable.L0 (spanCodes [278, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2838_orbit
  simpa only [lower470] using h

theorem space2839_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [279, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(279, 382), (96, 276), (10, 96)]
    (codeMat 87) (codeMat 354) (codeMat 142) false
    det87 det354 inv354
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space2839_lower : 18 ≤ frozenWangTable.L0 (spanCodes [279, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space2839_orbit
  simpa only [lower476] using h

theorem space2840_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [289, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(289, 10), (96, 30), (10, 191)]
    (codeMat 335) (codeMat 187) (codeMat 229) true
    det335 det187 inv187
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2840_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2840_orbit
  simpa only [lower456] using h

theorem space2841_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [290, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(290, 274), (96, 19), (10, 280)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    det84 det169 inv169
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space2841_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space2841_orbit
  simpa only [lower451] using h

theorem space2842_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [291, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(291, 449), (96, 20), (10, 479)]
    (codeMat 167) (codeMat 158) (codeMat 358) true
    det167 det158 inv158
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space2842_lower : 18 ≤ frozenWangTable.L0 (spanCodes [291, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space2842_orbit
  simpa only [lower457] using h

theorem space2843_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [294, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(294, 450), (96, 10), (10, 476)]
    (codeMat 244) (codeMat 143) (codeMat 482) true
    det244 det143 inv143
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space2843_lower : 18 ≤ frozenWangTable.L0 (spanCodes [294, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space2843_orbit
  simpa only [lower458] using h

theorem space2844_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [295, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(295, 456), (96, 10), (10, 476)]
    (codeMat 230) (codeMat 171) (codeMat 485) true
    det230 det171 inv171
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space2844_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space2844_orbit
  simpa only [lower458] using h

theorem space2845_orbit :
    frozenWangTable.OrbitImage 456 (spanCodes [304, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 456 [(304, 20), (96, 30), (10, 191)]
    (codeMat 230) (codeMat 369) (codeMat 377) false
    det230 det369 inv369
    (by rw [basis456]; decide +kernel)
    (by rw [basis456]; decide +kernel)

theorem space2845_lower : 18 ≤ frozenWangTable.L0 (spanCodes [304, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 456 space2845_orbit
  simpa only [lower456] using h

theorem space2846_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [305, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(305, 94), (96, 10), (10, 289)]
    (codeMat 354) (codeMat 161) (codeMat 161) false
    det354 det161 inv161
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2846_lower : 18 ≤ frozenWangTable.L0 (spanCodes [305, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2846_orbit
  simpa only [lower471] using h

theorem space2847_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [306, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(306, 469), (96, 10), (10, 449)]
    (codeMat 98) (codeMat 179) (codeMat 421) false
    det98 det179 inv179
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space2847_lower : 18 ≤ frozenWangTable.L0 (spanCodes [306, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space2847_orbit
  simpa only [lower457] using h


end QiushiMatmul.FrozenWang
