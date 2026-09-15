import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2848_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [307, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(307, 369), (96, 10), (10, 293)]
    (codeMat 370) (codeMat 165) (codeMat 163) false
    det370 det165 inv165
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space2848_lower : 18 ≤ frozenWangTable.L0 (spanCodes [307, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space2848_orbit
  simpa only [lower473] using h

theorem space2849_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [308, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(308, 175), (96, 197), (10, 96)]
    (codeMat 107) (codeMat 468) (codeMat 87) true
    det107 det468 inv468
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2849_lower : 18 ≤ frozenWangTable.L0 (spanCodes [308, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2849_orbit
  simpa only [lower475] using h

theorem space2850_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [309, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(309, 106), (96, 197), (10, 96)]
    (codeMat 123) (codeMat 212) (codeMat 86) true
    det123 det212 inv212
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2850_lower : 18 ≤ frozenWangTable.L0 (spanCodes [309, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2850_orbit
  simpa only [lower475] using h

theorem space2851_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [310, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(310, 294), (96, 376), (10, 300)]
    (codeMat 407) (codeMat 225) (codeMat 169) false
    det407 det225 inv225
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2851_lower : 18 ≤ frozenWangTable.L0 (spanCodes [310, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2851_orbit
  simpa only [lower474] using h

theorem space2852_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [311, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(311, 94), (96, 376), (10, 300)]
    (codeMat 277) (codeMat 485) (codeMat 171) false
    det277 det485 inv485
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2852_lower : 18 ≤ frozenWangTable.L0 (spanCodes [311, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2852_orbit
  simpa only [lower474] using h

theorem space2853_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [385, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(385, 96), (96, 10), (10, 276)]
    (codeMat 84) (codeMat 142) (codeMat 354) true
    det84 det142 inv142
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space2853_lower : 18 ≤ frozenWangTable.L0 (spanCodes [385, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space2853_orbit
  simpa only [lower476] using h

theorem space2854_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [386, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(386, 96), (96, 20), (10, 126)]
    (codeMat 358) (codeMat 330) (codeMat 394) false
    det358 det330 inv330
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2854_lower : 18 ≤ frozenWangTable.L0 (spanCodes [386, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2854_orbit
  simpa only [lower454] using h

theorem space2855_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [387, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(387, 10), (96, 265), (10, 349)]
    (codeMat 397) (codeMat 465) (codeMat 465) false
    det397 det465 inv465
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2855_lower : 18 ≤ frozenWangTable.L0 (spanCodes [387, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2855_orbit
  simpa only [lower470] using h

theorem space2856_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [388, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(388, 68), (96, 78), (10, 240)]
    (codeMat 92) (codeMat 206) (codeMat 498) false
    det92 det206 inv206
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2856_lower : 18 ≤ frozenWangTable.L0 (spanCodes [388, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2856_orbit
  simpa only [lower464] using h

theorem space2857_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [389, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(389, 265), (96, 349), (10, 259)]
    (codeMat 115) (codeMat 443) (codeMat 254) false
    det115 det443 inv443
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2857_lower : 18 ≤ frozenWangTable.L0 (spanCodes [389, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2857_orbit
  simpa only [lower470] using h

theorem space2858_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [391, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(391, 349), (96, 343), (10, 265)]
    (codeMat 239) (codeMat 225) (codeMat 169) false
    det239 det225 inv225
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2858_lower : 18 ≤ frozenWangTable.L0 (spanCodes [391, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2858_orbit
  simpa only [lower470] using h

theorem space2859_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [400, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(400, 10), (96, 20), (10, 126)]
    (codeMat 500) (codeMat 106) (codeMat 396) false
    det500 det106 inv106
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space2859_lower : 18 ≤ frozenWangTable.L0 (spanCodes [400, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space2859_orbit
  simpa only [lower454] using h

theorem space2860_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [401, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(401, 94), (96, 265), (10, 349)]
    (codeMat 271) (codeMat 213) (codeMat 470) false
    det271 det213 inv213
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2860_lower : 18 ≤ frozenWangTable.L0 (spanCodes [401, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2860_orbit
  simpa only [lower470] using h

theorem space2861_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [403, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(403, 382), (96, 10), (10, 276)]
    (codeMat 86) (codeMat 174) (codeMat 359) true
    det86 det174 inv174
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space2861_lower : 18 ≤ frozenWangTable.L0 (spanCodes [403, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 476 space2861_orbit
  simpa only [lower476] using h

theorem space2862_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [404, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(404, 259), (96, 343), (10, 265)]
    (codeMat 253) (codeMat 485) (codeMat 171) false
    det253 det485 inv485
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2862_lower : 18 ≤ frozenWangTable.L0 (spanCodes [404, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2862_orbit
  simpa only [lower470] using h

theorem space2863_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [406, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(406, 343), (96, 349), (10, 259)]
    (codeMat 99) (codeMat 415) (codeMat 253) false
    det99 det415 inv415
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2863_lower : 18 ≤ frozenWangTable.L0 (spanCodes [406, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2863_orbit
  simpa only [lower470] using h

theorem space2864_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [407, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(407, 250), (96, 78), (10, 240)]
    (codeMat 94) (codeMat 494) (codeMat 501) false
    det94 det494 inv494
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2864_lower : 18 ≤ frozenWangTable.L0 (spanCodes [407, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2864_orbit
  simpa only [lower464] using h

theorem space2865_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [417, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(417, 207), (96, 175), (10, 197)]
    (codeMat 107) (codeMat 501) (codeMat 494) false
    det107 det501 inv501
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2865_lower : 18 ≤ frozenWangTable.L0 (spanCodes [417, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2865_orbit
  simpa only [lower475] using h

theorem space2866_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [418, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(418, 476), (96, 20), (10, 450)]
    (codeMat 98) (codeMat 410) (codeMat 331) false
    det98 det410 inv410
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space2866_lower : 18 ≤ frozenWangTable.L0 (spanCodes [418, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space2866_orbit
  simpa only [lower458] using h

theorem space2867_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [419, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(419, 84), (96, 376), (10, 294)]
    (codeMat 419) (codeMat 412) (codeMat 111) false
    det419 det412 inv412
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2867_lower : 18 ≤ frozenWangTable.L0 (spanCodes [419, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2867_orbit
  simpa only [lower474] using h

theorem space2868_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [420, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(420, 10), (96, 78), (10, 383)]
    (codeMat 124) (codeMat 93) (codeMat 372) false
    det124 det93 inv93
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2868_lower : 18 ≤ frozenWangTable.L0 (spanCodes [420, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2868_orbit
  simpa only [lower466] using h

theorem space2869_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [421, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(421, 299), (96, 289), (10, 383)]
    (codeMat 236) (codeMat 337) (codeMat 337) false
    det236 det337 inv337
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2869_lower : 18 ≤ frozenWangTable.L0 (spanCodes [421, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2869_orbit
  simpa only [lower471] using h

theorem space2870_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [422, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(422, 300), (96, 10), (10, 376)]
    (codeMat 212) (codeMat 142) (codeMat 354) false
    det212 det142 inv142
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2870_lower : 18 ≤ frozenWangTable.L0 (spanCodes [422, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2870_orbit
  simpa only [lower474] using h

theorem space2871_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [433, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(433, 96), (96, 175), (10, 197)]
    (codeMat 123) (codeMat 241) (codeMat 489) false
    det123 det241 inv241
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space2871_lower : 18 ≤ frozenWangTable.L0 (spanCodes [433, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 475 space2871_orbit
  simpa only [lower475] using h

theorem space2872_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [434, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(434, 456), (96, 20), (10, 450)]
    (codeMat 114) (codeMat 442) (codeMat 334) false
    det114 det442 inv442
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space2872_lower : 18 ≤ frozenWangTable.L0 (spanCodes [434, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space2872_orbit
  simpa only [lower458] using h

theorem space2873_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [435, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(435, 300), (96, 376), (10, 294)]
    (codeMat 307) (codeMat 444) (codeMat 110) false
    det307 det444 inv444
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2873_lower : 18 ≤ frozenWangTable.L0 (spanCodes [435, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2873_orbit
  simpa only [lower474] using h

theorem space2874_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [436, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(436, 10), (96, 289), (10, 383)]
    (codeMat 254) (codeMat 85) (codeMat 340) false
    det254 det85 inv85
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2874_lower : 18 ≤ frozenWangTable.L0 (spanCodes [436, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2874_orbit
  simpa only [lower471] using h

theorem space2875_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [437, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(437, 68), (96, 78), (10, 383)]
    (codeMat 110) (codeMat 377) (codeMat 369) false
    det110 det377 inv377
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2875_lower : 18 ≤ frozenWangTable.L0 (spanCodes [437, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2875_orbit
  simpa only [lower466] using h

theorem space2876_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [439, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(439, 294), (96, 10), (10, 376)]
    (codeMat 214) (codeMat 174) (codeMat 359) false
    det214 det174 inv174
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2876_lower : 18 ≤ frozenWangTable.L0 (spanCodes [439, 96, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2876_orbit
  simpa only [lower474] using h

theorem space2877_orbit :
    frozenWangTable.OrbitImage 430 (spanCodes [96, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 430 [(96, 100), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    det267 det275 inv275
    (by rw [basis430]; decide +kernel)
    (by rw [basis430]; decide +kernel)

theorem space2877_lower : 17 ≤ frozenWangTable.L0 (spanCodes [96, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 430 space2877_orbit
  simpa only [lower430] using h

theorem space2878_orbit :
    frozenWangTable.OrbitImage 430 (spanCodes [96, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 430 [(96, 100), (18, 16), (10, 17)]
    (codeMat 282) (codeMat 281) (codeMat 281) true
    det282 det281 inv281
    (by rw [basis430]; decide +kernel)
    (by rw [basis430]; decide +kernel)

theorem space2878_lower : 17 ≤ frozenWangTable.L0 (spanCodes [96, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 430 space2878_orbit
  simpa only [lower430] using h

theorem space2879_orbit :
    frozenWangTable.OrbitImage 295 (spanCodes [96, 20, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 295 [(96, 315), (20, 42), (9, 32), (3, 1)]
    (codeMat 345) (codeMat 486) (codeMat 157) false
    det345 det486 inv486
    (by rw [basis295]; decide +kernel)
    (by rw [basis295]; decide +kernel)

theorem space2879_lower : 17 ≤ frozenWangTable.L0 (spanCodes [96, 20, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 295 space2879_orbit
  simpa only [lower295] using h


end QiushiMatmul.FrozenWang
