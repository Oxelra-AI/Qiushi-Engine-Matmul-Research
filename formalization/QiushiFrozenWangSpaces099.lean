import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3168_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 166, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 20), (166, 10), (10, 476)]
    (codeMat 110) (codeMat 122) (codeMat 460) true
    det110 det122 inv122
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3168_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 166, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3168_orbit
  simpa only [lower458] using h

theorem space3169_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 167, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 10), (167, 94), (10, 294)]
    (codeMat 481) (codeMat 84) (codeMat 84) false
    det481 det84 inv84
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3169_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 167, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3169_orbit
  simpa only [lower474] using h

theorem space3170_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 176, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 80), (176, 10), (10, 78)]
    (codeMat 354) (codeMat 110) (codeMat 444) false
    det354 det110 inv110
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3170_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 176, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3170_orbit
  simpa only [lower453] using h

theorem space3171_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 177, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 265), (177, 94), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) false
    det282 det267 inv267
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3171_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 177, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3171_orbit
  simpa only [lower470] using h

theorem space3172_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 179, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 300), (179, 84), (10, 10)]
    (codeMat 458) (codeMat 266) (codeMat 266) false
    det458 det266 inv266
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3172_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 179, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3172_orbit
  simpa only [lower474] using h

theorem space3173_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 181, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 343), (181, 84), (10, 349)]
    (codeMat 470) (codeMat 171) (codeMat 485) false
    det470 det171 inv171
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3173_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 181, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3173_orbit
  simpa only [lower470] using h

theorem space3174_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 182, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 10), (182, 20), (10, 479)]
    (codeMat 229) (codeMat 117) (codeMat 380) true
    det229 det117 inv117
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3174_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 182, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3174_orbit
  simpa only [lower457] using h

theorem space3175_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 183, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 315), (183, 305), (10, 383)]
    (codeMat 190) (codeMat 467) (codeMat 339) false
    det190 det467 inv467
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3175_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 183, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3175_orbit
  simpa only [lower466] using h

theorem space3176_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 193, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 30), (193, 10), (10, 80)]
    (codeMat 204) (codeMat 307) (codeMat 311) false
    det204 det307 inv307
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3176_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 193, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3176_orbit
  simpa only [lower453] using h

theorem space3177_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 196, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 30), (196, 20), (10, 96)]
    (codeMat 205) (codeMat 419) (codeMat 183) false
    det205 det419 inv419
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3177_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 196, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3177_orbit
  simpa only [lower454] using h

theorem space3178_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 198, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 10), (198, 30), (10, 456)]
    (codeMat 140) (codeMat 107) (codeMat 428) false
    det140 det107 inv107
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3178_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 198, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3178_orbit
  simpa only [lower458] using h

theorem space3179_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 199, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 30), (199, 10), (10, 449)]
    (codeMat 225) (codeMat 253) (codeMat 415) false
    det225 det253 inv253
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3179_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 199, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3179_orbit
  simpa only [lower457] using h

theorem space3180_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 208, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 78), (208, 10), (10, 80)]
    (codeMat 212) (codeMat 299) (codeMat 318) false
    det212 det299 inv299
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space3180_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 208, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space3180_orbit
  simpa only [lower453] using h

theorem space3181_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 211, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 469), (211, 30), (10, 20)]
    (codeMat 206) (codeMat 279) (codeMat 279) true
    det206 det279 inv279
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3181_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 211, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3181_orbit
  simpa only [lower457] using h

theorem space3182_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 212, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 10), (212, 94), (10, 265)]
    (codeMat 172) (codeMat 102) (codeMat 156) false
    det172 det102 inv102
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3182_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 212, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3182_orbit
  simpa only [lower470] using h

theorem space3183_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 213, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 349), (213, 84), (10, 343)]
    (codeMat 486) (codeMat 174) (codeMat 359) false
    det486 det174 inv174
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3183_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 213, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3183_orbit
  simpa only [lower470] using h

theorem space3184_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 214, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 10), (214, 84), (10, 300)]
    (codeMat 460) (codeMat 98) (codeMat 140) false
    det460 det98 inv98
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3184_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 214, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3184_orbit
  simpa only [lower474] using h

theorem space3185_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 215, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 373), (215, 305), (10, 383)]
    (codeMat 230) (codeMat 174) (codeMat 359) false
    det230 det174 inv174
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3185_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 215, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3185_orbit
  simpa only [lower466] using h

theorem space3186_orbit :
    frozenWangTable.OrbitImage 454 (spanCodes [258, 224, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 454 [(258, 126), (224, 20), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    det214 det355 inv355
    (by rw [basis454]; decide +kernel)
    (by rw [basis454]; decide +kernel)

theorem space3186_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 224, 10]) := by
  have h := frozenWangTable.lower_le_L0 454 space3186_orbit
  simpa only [lower454] using h

theorem space3187_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 225, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 259), (225, 94), (10, 265)]
    (codeMat 116) (codeMat 165) (codeMat 163) false
    det116 det165 inv165
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3187_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 225, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3187_orbit
  simpa only [lower470] using h

theorem space3188_orbit :
    frozenWangTable.OrbitImage 458 (spanCodes [258, 226, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 458 [(258, 450), (226, 470), (10, 456)]
    (codeMat 84) (codeMat 179) (codeMat 421) false
    det84 det179 inv179
    (by rw [basis458]; decide +kernel)
    (by rw [basis458]; decide +kernel)

theorem space3188_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 226, 10]) := by
  have h := frozenWangTable.lower_le_L0 458 space3188_orbit
  simpa only [lower458] using h

theorem space3189_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [258, 227, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(258, 294), (227, 376), (10, 300)]
    (codeMat 468) (codeMat 161) (codeMat 161) false
    det468 det161 inv161
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space3189_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 227, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space3189_orbit
  simpa only [lower474] using h

theorem space3190_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [258, 228, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(258, 240), (228, 78), (10, 68)]
    (codeMat 107) (codeMat 482) (codeMat 143) false
    det107 det482 inv482
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space3190_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 228, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space3190_orbit
  simpa only [lower464] using h

theorem space3191_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 229, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 349), (229, 84), (10, 10)]
    (codeMat 459) (codeMat 286) (codeMat 303) false
    det459 det286 inv286
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3191_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 229, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3191_orbit
  simpa only [lower470] using h

theorem space3192_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [258, 230, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(258, 383), (230, 94), (10, 10)]
    (codeMat 339) (codeMat 285) (codeMat 317) false
    det339 det285 inv285
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space3192_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 230, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space3192_orbit
  simpa only [lower471] using h

theorem space3193_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 231, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 383), (231, 78), (10, 68)]
    (codeMat 123) (codeMat 486) (codeMat 157) false
    det123 det486 inv486
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3193_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 231, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3193_orbit
  simpa only [lower466] using h

theorem space3194_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 241, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 10), (241, 84), (10, 343)]
    (codeMat 485) (codeMat 117) (codeMat 380) false
    det485 det117 inv117
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3194_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 241, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3194_orbit
  simpa only [lower470] using h

theorem space3195_orbit :
    frozenWangTable.OrbitImage 457 (spanCodes [258, 242, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 457 [(258, 479), (242, 459), (10, 449)]
    (codeMat 226) (codeMat 254) (codeMat 443) false
    det226 det254 inv254
    (by rw [basis457]; decide +kernel)
    (by rw [basis457]; decide +kernel)

theorem space3195_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 242, 10]) := by
  have h := frozenWangTable.lower_le_L0 457 space3195_orbit
  simpa only [lower457] using h

theorem space3196_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 243, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 10), (243, 78), (10, 383)]
    (codeMat 229) (codeMat 117) (codeMat 380) false
    det229 det117 inv117
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3196_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 243, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3196_orbit
  simpa only [lower466] using h

theorem space3197_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [258, 244, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(258, 343), (244, 84), (10, 10)]
    (codeMat 467) (codeMat 285) (codeMat 317) false
    det467 det285 inv285
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space3197_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 244, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space3197_orbit
  simpa only [lower470] using h

theorem space3198_orbit :
    frozenWangTable.OrbitImage 462 (spanCodes [258, 245, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 462 [(258, 68), (245, 10), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    det93 det459 inv459
    (by rw [basis462]; decide +kernel)
    (by rw [basis462]; decide +kernel)

theorem space3198_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 245, 10]) := by
  have h := frozenWangTable.lower_le_L0 462 space3198_orbit
  simpa only [lower462] using h

theorem space3199_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [258, 246, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(258, 315), (246, 10), (10, 68)]
    (codeMat 187) (codeMat 485) (codeMat 171) false
    det187 det485 inv485
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space3199_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 246, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space3199_orbit
  simpa only [lower466] using h


end QiushiMatmul.FrozenWang
