import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2080_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [305, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(305, 305), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2080_lower : 18 ≤ frozenWangTable.L0 (spanCodes [305, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2080_orbit
  simpa only [lower466] using h

theorem space2081_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [306, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(306, 315), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    det185 det421 inv421
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2081_lower : 18 ≤ frozenWangTable.L0 (spanCodes [306, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2081_orbit
  simpa only [lower466] using h

theorem space2082_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [307, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(307, 314), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    det185 det421 inv421
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2082_lower : 18 ≤ frozenWangTable.L0 (spanCodes [307, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2082_orbit
  simpa only [lower465] using h

theorem space2083_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [308, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(308, 373), (68, 78), (10, 68)]
    (codeMat 249) (codeMat 419) (codeMat 183) false
    det249 det419 inv419
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2083_lower : 18 ≤ frozenWangTable.L0 (spanCodes [308, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2083_orbit
  simpa only [lower466] using h

theorem space2084_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [309, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(309, 372), (68, 78), (10, 68)]
    (codeMat 249) (codeMat 419) (codeMat 183) false
    det249 det419 inv419
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2084_lower : 18 ≤ frozenWangTable.L0 (spanCodes [309, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2084_orbit
  simpa only [lower465] using h

theorem space2085_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [310, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(310, 383), (68, 78), (10, 68)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    det241 det423 inv423
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2085_lower : 18 ≤ frozenWangTable.L0 (spanCodes [310, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2085_orbit
  simpa only [lower466] using h

theorem space2086_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [311, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(311, 382), (68, 78), (10, 68)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    det241 det423 inv423
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2086_lower : 18 ≤ frozenWangTable.L0 (spanCodes [311, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2086_orbit
  simpa only [lower465] using h

theorem space2087_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [385, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(385, 10), (68, 20), (10, 149)]
    (codeMat 417) (codeMat 394) (codeMat 330) false
    det417 det394 inv394
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2087_lower : 18 ≤ frozenWangTable.L0 (spanCodes [385, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2087_orbit
  simpa only [lower455] using h

theorem space2088_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [386, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(386, 30), (68, 20), (10, 149)]
    (codeMat 489) (codeMat 426) (codeMat 335) false
    det489 det426 inv426
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2088_lower : 18 ≤ frozenWangTable.L0 (spanCodes [386, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2088_orbit
  simpa only [lower455] using h

theorem space2089_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [389, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(389, 30), (68, 20), (10, 149)]
    (codeMat 481) (codeMat 410) (codeMat 331) false
    det481 det410 inv410
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2089_lower : 18 ≤ frozenWangTable.L0 (spanCodes [389, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2089_orbit
  simpa only [lower455] using h

theorem space2090_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [391, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(391, 10), (68, 20), (10, 149)]
    (codeMat 425) (codeMat 442) (codeMat 334) false
    det425 det442 inv442
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2090_lower : 18 ≤ frozenWangTable.L0 (spanCodes [391, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2090_orbit
  simpa only [lower455] using h

theorem space2091_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [400, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(400, 304), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2091_lower : 18 ≤ frozenWangTable.L0 (spanCodes [400, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2091_orbit
  simpa only [lower465] using h

theorem space2092_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [401, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(401, 305), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2092_lower : 18 ≤ frozenWangTable.L0 (spanCodes [401, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2092_orbit
  simpa only [lower466] using h

theorem space2093_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [402, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(402, 315), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    det169 det165 inv165
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2093_lower : 18 ≤ frozenWangTable.L0 (spanCodes [402, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2093_orbit
  simpa only [lower466] using h

theorem space2094_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [403, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(403, 314), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    det169 det165 inv165
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2094_lower : 18 ≤ frozenWangTable.L0 (spanCodes [403, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2094_orbit
  simpa only [lower465] using h

theorem space2095_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [404, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(404, 383), (68, 10), (10, 68)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    det225 det163 inv163
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2095_lower : 18 ≤ frozenWangTable.L0 (spanCodes [404, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2095_orbit
  simpa only [lower466] using h

theorem space2096_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [405, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(405, 382), (68, 10), (10, 68)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    det225 det163 inv163
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2096_lower : 18 ≤ frozenWangTable.L0 (spanCodes [405, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2096_orbit
  simpa only [lower465] using h

theorem space2097_orbit :
    frozenWangTable.OrbitImage 466 (spanCodes [406, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 466 [(406, 373), (68, 10), (10, 68)]
    (codeMat 233) (codeMat 167) (codeMat 167) false
    det233 det167 inv167
    (by rw [basis466]; decide +kernel)
    (by rw [basis466]; decide +kernel)

theorem space2097_lower : 18 ≤ frozenWangTable.L0 (spanCodes [406, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 466 space2097_orbit
  simpa only [lower466] using h

theorem space2098_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [407, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(407, 372), (68, 10), (10, 68)]
    (codeMat 233) (codeMat 167) (codeMat 167) false
    det233 det167 inv167
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2098_lower : 18 ≤ frozenWangTable.L0 (spanCodes [407, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2098_orbit
  simpa only [lower465] using h

theorem space2099_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [416, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(416, 68), (68, 10), (10, 168)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    det140 det142 inv142
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2099_lower : 18 ≤ frozenWangTable.L0 (spanCodes [416, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2099_orbit
  simpa only [lower461] using h

theorem space2100_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [417, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(417, 230), (68, 10), (10, 168)]
    (codeMat 141) (codeMat 174) (codeMat 359) false
    det141 det174 inv174
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2100_lower : 18 ≤ frozenWangTable.L0 (spanCodes [417, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2100_orbit
  simpa only [lower461] using h

theorem space2101_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [418, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(418, 180), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2101_lower : 18 ≤ frozenWangTable.L0 (spanCodes [418, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2101_orbit
  simpa only [lower464] using h

theorem space2102_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [419, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(419, 250), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    det169 det165 inv165
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2102_lower : 18 ≤ frozenWangTable.L0 (spanCodes [419, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2102_orbit
  simpa only [lower464] using h

theorem space2103_orbit :
    frozenWangTable.OrbitImage 462 (spanCodes [420, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 462 [(420, 78), (68, 10), (10, 184)]
    (codeMat 140) (codeMat 158) (codeMat 358) false
    det140 det158 inv158
    (by rw [basis462]; decide +kernel)
    (by rw [basis462]; decide +kernel)

theorem space2103_lower : 18 ≤ frozenWangTable.L0 (spanCodes [420, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 462 space2103_orbit
  simpa only [lower462] using h

theorem space2104_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [421, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(421, 179), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space2104_lower : 18 ≤ frozenWangTable.L0 (spanCodes [421, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space2104_orbit
  simpa only [lower463] using h

theorem space2105_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [422, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(422, 180), (68, 10), (10, 78)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    det417 det177 inv177
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2105_lower : 18 ≤ frozenWangTable.L0 (spanCodes [422, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2105_orbit
  simpa only [lower464] using h

theorem space2106_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [423, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(423, 250), (68, 10), (10, 78)]
    (codeMat 425) (codeMat 183) (codeMat 419) false
    det425 det183 inv183
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2106_lower : 18 ≤ frozenWangTable.L0 (spanCodes [423, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2106_orbit
  simpa only [lower464] using h

theorem space2107_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [434, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(434, 20), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2107_lower : 18 ≤ frozenWangTable.L0 (spanCodes [434, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2107_orbit
  simpa only [lower453] using h

theorem space2108_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [435, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(435, 30), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    det185 det421 inv421
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2108_lower : 18 ≤ frozenWangTable.L0 (spanCodes [435, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2108_orbit
  simpa only [lower453] using h

theorem space2109_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [436, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(436, 20), (68, 68), (10, 78)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    det305 det401 inv401
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2109_lower : 18 ≤ frozenWangTable.L0 (spanCodes [436, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2109_orbit
  simpa only [lower453] using h

theorem space2110_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [437, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(437, 30), (68, 68), (10, 78)]
    (codeMat 313) (codeMat 403) (codeMat 403) false
    det313 det403 inv403
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2110_lower : 18 ≤ frozenWangTable.L0 (spanCodes [437, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2110_orbit
  simpa only [lower453] using h

theorem space2111_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [439, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(439, 19), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space2111_lower : 18 ≤ frozenWangTable.L0 (spanCodes [439, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space2111_orbit
  simpa only [lower450] using h


end QiushiMatmul.FrozenWang
