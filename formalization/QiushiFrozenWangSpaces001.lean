import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0032_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [228, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(228, 68), (19, 19), (10, 10)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    det267 det282 inv282
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0032_lower : 18 ≤ frozenWangTable.L0 (spanCodes [228, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0032_orbit
  simpa only [lower450] using h

theorem space0033_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [229, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(229, 87), (19, 19), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    det267 det318 inv318
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0033_lower : 18 ≤ frozenWangTable.L0 (spanCodes [229, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0033_orbit
  simpa only [lower450] using h

theorem space0034_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [230, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(230, 93), (19, 19), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    det267 det286 inv286
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0034_lower : 18 ≤ frozenWangTable.L0 (spanCodes [230, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0034_orbit
  simpa only [lower450] using h

theorem space0035_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [231, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(231, 78), (19, 19), (10, 10)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    det267 det314 inv314
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space0035_lower : 18 ≤ frozenWangTable.L0 (spanCodes [231, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space0035_orbit
  simpa only [lower450] using h

theorem space0036_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [257, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(257, 280), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 281) (codeMat 281) false
    det266 det281 inv281
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0036_lower : 18 ≤ frozenWangTable.L0 (spanCodes [257, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0036_orbit
  simpa only [lower451] using h

theorem space0037_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [258, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(258, 280), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    det266 det275 inv275
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0037_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0037_orbit
  simpa only [lower451] using h

theorem space0038_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [259, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(259, 280), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0038_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0038_orbit
  simpa only [lower451] using h

theorem space0039_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [261, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(261, 280), (19, 10), (10, 19)]
    (codeMat 330) (codeMat 281) (codeMat 281) false
    det330 det281 inv281
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0039_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0039_orbit
  simpa only [lower451] using h

theorem space0040_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [262, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(262, 280), (19, 19), (10, 25)]
    (codeMat 330) (codeMat 275) (codeMat 275) false
    det330 det275 inv275
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0040_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0040_orbit
  simpa only [lower451] using h

theorem space0041_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [263, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(263, 280), (19, 25), (10, 10)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    det330 det266 inv266
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0041_lower : 18 ≤ frozenWangTable.L0 (spanCodes [263, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0041_orbit
  simpa only [lower451] using h

theorem space0042_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [289, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(289, 280), (19, 10), (10, 19)]
    (codeMat 394) (codeMat 281) (codeMat 281) false
    det394 det281 inv281
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0042_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0042_orbit
  simpa only [lower451] using h

theorem space0043_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [290, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(290, 280), (19, 19), (10, 25)]
    (codeMat 394) (codeMat 275) (codeMat 275) false
    det394 det275 inv275
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0043_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0043_orbit
  simpa only [lower451] using h

theorem space0044_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [291, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(291, 280), (19, 25), (10, 10)]
    (codeMat 394) (codeMat 266) (codeMat 266) false
    det394 det266 inv266
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0044_lower : 18 ≤ frozenWangTable.L0 (spanCodes [291, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0044_orbit
  simpa only [lower451] using h

theorem space0045_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [293, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(293, 280), (19, 10), (10, 19)]
    (codeMat 458) (codeMat 281) (codeMat 281) false
    det458 det281 inv281
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0045_lower : 18 ≤ frozenWangTable.L0 (spanCodes [293, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0045_orbit
  simpa only [lower451] using h

theorem space0046_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [294, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(294, 280), (19, 19), (10, 25)]
    (codeMat 458) (codeMat 275) (codeMat 275) false
    det458 det275 inv275
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0046_lower : 18 ≤ frozenWangTable.L0 (spanCodes [294, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0046_orbit
  simpa only [lower451] using h

theorem space0047_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [295, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(295, 280), (19, 25), (10, 10)]
    (codeMat 458) (codeMat 266) (codeMat 266) false
    det458 det266 inv266
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0047_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0047_orbit
  simpa only [lower451] using h

theorem space0048_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [321, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(321, 280), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 317) (codeMat 285) false
    det266 det317 inv317
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0048_lower : 18 ≤ frozenWangTable.L0 (spanCodes [321, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0048_orbit
  simpa only [lower451] using h

theorem space0049_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [322, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(322, 280), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 279) (codeMat 279) false
    det266 det279 inv279
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0049_lower : 18 ≤ frozenWangTable.L0 (spanCodes [322, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0049_orbit
  simpa only [lower451] using h

theorem space0050_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [323, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(323, 280), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    det266 det298 inv298
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0050_lower : 18 ≤ frozenWangTable.L0 (spanCodes [323, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0050_orbit
  simpa only [lower451] using h

theorem space0051_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [324, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(324, 280), (19, 10), (10, 19)]
    (codeMat 330) (codeMat 317) (codeMat 285) false
    det330 det317 inv317
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0051_lower : 18 ≤ frozenWangTable.L0 (spanCodes [324, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0051_orbit
  simpa only [lower451] using h

theorem space0052_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [326, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(326, 280), (19, 25), (10, 10)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    det330 det298 inv298
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0052_lower : 18 ≤ frozenWangTable.L0 (spanCodes [326, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0052_orbit
  simpa only [lower451] using h

theorem space0053_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [327, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(327, 280), (19, 19), (10, 25)]
    (codeMat 330) (codeMat 279) (codeMat 279) false
    det330 det279 inv279
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0053_lower : 18 ≤ frozenWangTable.L0 (spanCodes [327, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0053_orbit
  simpa only [lower451] using h

theorem space0054_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [352, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(352, 257), (19, 19), (10, 25)]
    (codeMat 394) (codeMat 279) (codeMat 279) false
    det394 det279 inv279
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0054_lower : 18 ≤ frozenWangTable.L0 (spanCodes [352, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0054_orbit
  simpa only [lower451] using h

theorem space0055_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [353, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(353, 274), (19, 25), (10, 10)]
    (codeMat 394) (codeMat 298) (codeMat 270) false
    det394 det298 inv298
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0055_lower : 18 ≤ frozenWangTable.L0 (spanCodes [353, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0055_orbit
  simpa only [lower451] using h

theorem space0056_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [355, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(355, 267), (19, 10), (10, 19)]
    (codeMat 394) (codeMat 317) (codeMat 285) false
    det394 det317 inv317
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0056_lower : 18 ≤ frozenWangTable.L0 (spanCodes [355, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0056_orbit
  simpa only [lower451] using h

theorem space0057_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [356, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(356, 274), (19, 25), (10, 10)]
    (codeMat 458) (codeMat 298) (codeMat 270) false
    det458 det298 inv298
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0057_lower : 18 ≤ frozenWangTable.L0 (spanCodes [356, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0057_orbit
  simpa only [lower451] using h

theorem space0058_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [357, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(357, 257), (19, 19), (10, 25)]
    (codeMat 458) (codeMat 279) (codeMat 279) false
    det458 det279 inv279
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0058_lower : 18 ≤ frozenWangTable.L0 (spanCodes [357, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0058_orbit
  simpa only [lower451] using h

theorem space0059_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [358, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(358, 267), (19, 10), (10, 19)]
    (codeMat 458) (codeMat 317) (codeMat 285) false
    det458 det317 inv317
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0059_lower : 18 ≤ frozenWangTable.L0 (spanCodes [358, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0059_orbit
  simpa only [lower451] using h

theorem space0060_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [385, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(385, 280), (19, 10), (10, 19)]
    (codeMat 266) (codeMat 313) (codeMat 313) false
    det266 det313 inv313
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0060_lower : 18 ≤ frozenWangTable.L0 (spanCodes [385, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0060_orbit
  simpa only [lower451] using h

theorem space0061_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [386, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(386, 280), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 311) (codeMat 307) false
    det266 det311 inv311
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0061_lower : 18 ≤ frozenWangTable.L0 (spanCodes [386, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0061_orbit
  simpa only [lower451] using h

theorem space0062_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [387, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(387, 280), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    det266 det270 inv270
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0062_lower : 18 ≤ frozenWangTable.L0 (spanCodes [387, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0062_orbit
  simpa only [lower451] using h

theorem space0063_orbit :
    frozenWangTable.OrbitImage 451 (spanCodes [388, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 451 [(388, 280), (19, 19), (10, 25)]
    (codeMat 330) (codeMat 311) (codeMat 307) false
    det330 det311 inv311
    (by rw [basis451]; decide +kernel)
    (by rw [basis451]; decide +kernel)

theorem space0063_lower : 18 ≤ frozenWangTable.L0 (spanCodes [388, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 451 space0063_orbit
  simpa only [lower451] using h


end QiushiMatmul.FrozenWang
