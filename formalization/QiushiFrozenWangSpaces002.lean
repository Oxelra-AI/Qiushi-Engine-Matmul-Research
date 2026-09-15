import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0064_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [389, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(389, 280), (19, 25), (10, 10)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    det330 det270 inv270
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0064_lower : 18 ≤ frozenWangTable.L0 (spanCodes [389, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0064_orbit
  simpa only [lower451] using h

theorem space0065_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [391, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(391, 280), (19, 10), (10, 19)]
    (codeMat 330) (codeMat 313) (codeMat 313) false
    det330 det313 inv313
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0065_lower : 18 ≤ frozenWangTable.L0 (spanCodes [391, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0065_orbit
  simpa only [lower451] using h

theorem space0066_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [416, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(416, 257), (19, 25), (10, 10)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    det394 det270 inv270
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0066_lower : 18 ≤ frozenWangTable.L0 (spanCodes [416, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0066_orbit
  simpa only [lower451] using h

theorem space0067_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [417, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(417, 267), (19, 19), (10, 25)]
    (codeMat 394) (codeMat 311) (codeMat 307) false
    det394 det311 inv311
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0067_lower : 18 ≤ frozenWangTable.L0 (spanCodes [417, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0067_orbit
  simpa only [lower451] using h

theorem space0068_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [418, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(418, 274), (19, 10), (10, 19)]
    (codeMat 394) (codeMat 313) (codeMat 313) false
    det394 det313 inv313
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0068_lower : 18 ≤ frozenWangTable.L0 (spanCodes [418, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0068_orbit
  simpa only [lower451] using h

theorem space0069_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [420, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(420, 274), (19, 10), (10, 19)]
    (codeMat 458) (codeMat 313) (codeMat 313) false
    det458 det313 inv313
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0069_lower : 18 ≤ frozenWangTable.L0 (spanCodes [420, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0069_orbit
  simpa only [lower451] using h

theorem space0070_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [422, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(422, 257), (19, 25), (10, 10)]
    (codeMat 458) (codeMat 270) (codeMat 298) false
    det458 det270 inv270
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0070_lower : 18 ≤ frozenWangTable.L0 (spanCodes [422, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0070_orbit
  simpa only [lower451] using h

theorem space0071_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [423, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(423, 267), (19, 19), (10, 25)]
    (codeMat 458) (codeMat 311) (codeMat 307) false
    det458 det311 inv311
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0071_lower : 18 ≤ frozenWangTable.L0 (spanCodes [423, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0071_orbit
  simpa only [lower451] using h

theorem space0072_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [449, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(449, 280), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 285) (codeMat 317) false
    det266 det285 inv285
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0072_lower : 18 ≤ frozenWangTable.L0 (spanCodes [449, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0072_orbit
  simpa only [lower451] using h

theorem space0073_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [450, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(450, 280), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 307) (codeMat 311) false
    det266 det307 inv307
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0073_lower : 18 ≤ frozenWangTable.L0 (spanCodes [450, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0073_orbit
  simpa only [lower451] using h

theorem space0074_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [451, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(451, 280), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0074_lower : 18 ≤ frozenWangTable.L0 (spanCodes [451, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0074_orbit
  simpa only [lower451] using h

theorem space0075_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [452, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(452, 280), (19, 25), (10, 10)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    det330 det302 inv302
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0075_lower : 18 ≤ frozenWangTable.L0 (spanCodes [452, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0075_orbit
  simpa only [lower451] using h

theorem space0076_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [453, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(453, 280), (19, 19), (10, 25)]
    (codeMat 330) (codeMat 307) (codeMat 311) false
    det330 det307 inv307
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0076_lower : 18 ≤ frozenWangTable.L0 (spanCodes [453, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0076_orbit
  simpa only [lower451] using h

theorem space0077_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [454, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(454, 280), (19, 10), (10, 19)]
    (codeMat 330) (codeMat 285) (codeMat 317) false
    det330 det285 inv285
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0077_lower : 18 ≤ frozenWangTable.L0 (spanCodes [454, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0077_orbit
  simpa only [lower451] using h

theorem space0078_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [480, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(480, 257), (19, 10), (10, 19)]
    (codeMat 394) (codeMat 285) (codeMat 317) false
    det394 det285 inv285
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0078_lower : 18 ≤ frozenWangTable.L0 (spanCodes [480, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0078_orbit
  simpa only [lower451] using h

theorem space0079_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [482, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(482, 267), (19, 25), (10, 10)]
    (codeMat 394) (codeMat 302) (codeMat 302) false
    det394 det302 inv302
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0079_lower : 18 ≤ frozenWangTable.L0 (spanCodes [482, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0079_orbit
  simpa only [lower451] using h

theorem space0080_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [483, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(483, 274), (19, 19), (10, 25)]
    (codeMat 394) (codeMat 307) (codeMat 311) false
    det394 det307 inv307
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0080_lower : 18 ≤ frozenWangTable.L0 (spanCodes [483, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0080_orbit
  simpa only [lower451] using h

theorem space0081_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [484, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(484, 274), (19, 19), (10, 25)]
    (codeMat 458) (codeMat 307) (codeMat 311) false
    det458 det307 inv307
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0081_lower : 18 ≤ frozenWangTable.L0 (spanCodes [484, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0081_orbit
  simpa only [lower451] using h

theorem space0082_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [485, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(485, 267), (19, 25), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    det458 det302 inv302
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0082_lower : 18 ≤ frozenWangTable.L0 (spanCodes [485, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0082_orbit
  simpa only [lower451] using h

theorem space0083_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [487, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(487, 257), (19, 10), (10, 19)]
    (codeMat 458) (codeMat 285) (codeMat 317) false
    det458 det285 inv285
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0083_lower : 18 ≤ frozenWangTable.L0 (spanCodes [487, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0083_orbit
  simpa only [lower451] using h

theorem space0084_orbit :
    frozenWangTable.OrbitImage 417 (spanCodes [18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 417 [(18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    det266 det282 inv282
    (by rw [basis417]; decide +kernel)
    (by rw [basis417]; decide +kernel)

theorem space0084_lower : 17 ≤ frozenWangTable.L0 (spanCodes [18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 417 space0084_orbit
  simpa only [lower417] using h

theorem space0085_orbit :
    frozenWangTable.OrbitImage 417 (spanCodes [17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 417 [(17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis417]; decide +kernel)
    (by rw [basis417]; decide +kernel)

theorem space0085_lower : 17 ≤ frozenWangTable.L0 (spanCodes [17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 417 space0085_orbit
  simpa only [lower417] using h

theorem space0086_orbit :
    frozenWangTable.OrbitImage 417 (spanCodes [16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 417 [(16, 1), (9, 27), (3, 16)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    det266 det267 inv267
    (by rw [basis417]; decide +kernel)
    (by rw [basis417]; decide +kernel)

theorem space0086_lower : 17 ≤ frozenWangTable.L0 (spanCodes [16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 417 space0086_orbit
  simpa only [lower417] using h

theorem space0087_orbit :
    frozenWangTable.OrbitImage 279 (spanCodes [68, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 279 [(68, 68), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    det273 det275 inv275
    (by rw [basis279]; decide +kernel)
    (by rw [basis279]; decide +kernel)

theorem space0087_lower : 17 ≤ frozenWangTable.L0 (spanCodes [68, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 279 space0087_orbit
  simpa only [lower279] using h

theorem space0088_orbit :
    frozenWangTable.OrbitImage 279 (spanCodes [70, 18, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 279 [(70, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    det273 det307 inv307
    (by rw [basis279]; decide +kernel)
    (by rw [basis279]; decide +kernel)

theorem space0088_lower : 17 ≤ frozenWangTable.L0 (spanCodes [70, 18, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 279 space0088_orbit
  simpa only [lower279] using h

theorem space0089_orbit :
    frozenWangTable.OrbitImage 279 (spanCodes [96, 17, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 279 [(96, 68), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis279]; decide +kernel)
    (by rw [basis279]; decide +kernel)

theorem space0089_lower : 17 ≤ frozenWangTable.L0 (spanCodes [96, 17, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 279 space0089_orbit
  simpa only [lower279] using h

theorem space0090_orbit :
    frozenWangTable.OrbitImage 279 (spanCodes [101, 16, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 279 [(101, 78), (16, 27), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 307) (codeMat 311) false
    det267 det307 inv307
    (by rw [basis279]; decide +kernel)
    (by rw [basis279]; decide +kernel)

theorem space0090_lower : 17 ≤ frozenWangTable.L0 (spanCodes [101, 16, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 279 space0090_orbit
  simpa only [lower279] using h

theorem space0091_orbit :
    frozenWangTable.OrbitImage 435 (spanCodes [193, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 435 [(193, 39), (19, 20), (10, 50)]
    (codeMat 86) (codeMat 281) (codeMat 281) true
    det86 det281 inv281
    (by rw [basis435]; decide +kernel)
    (by rw [basis435]; decide +kernel)

theorem space0091_lower : 17 ≤ frozenWangTable.L0 (spanCodes [193, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 435 space0091_orbit
  simpa only [lower435] using h

theorem space0092_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [256, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(256, 1), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0092_lower : 17 ≤ frozenWangTable.L0 (spanCodes [256, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0092_orbit
  simpa only [lower446] using h

theorem space0093_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [260, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(260, 1), (19, 400), (10, 160)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    det85 det84 inv84
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0093_lower : 17 ≤ frozenWangTable.L0 (spanCodes [260, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0093_orbit
  simpa only [lower446] using h

theorem space0094_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [288, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(288, 1), (19, 400), (10, 160)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    det86 det84 inv84
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0094_lower : 17 ≤ frozenWangTable.L0 (spanCodes [288, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0094_orbit
  simpa only [lower446] using h

theorem space0095_orbit :
    frozenWangTable.OrbitImage 446 (spanCodes [292, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 446 [(292, 1), (19, 400), (10, 160)]
    (codeMat 87) (codeMat 84) (codeMat 84) false
    det87 det84 inv84
    (by rw [basis446]; decide +kernel)
    (by rw [basis446]; decide +kernel)

theorem space0095_lower : 17 ≤ frozenWangTable.L0 (spanCodes [292, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 446 space0095_orbit
  simpa only [lower446] using h


end QiushiMatmul.FrozenWang
