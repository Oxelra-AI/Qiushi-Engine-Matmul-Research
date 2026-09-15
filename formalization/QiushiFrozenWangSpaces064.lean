import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2048_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [162, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(162, 162), (68, 68), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2048_lower : 18 ≤ frozenWangTable.L0 (spanCodes [162, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2048_orbit
  simpa only [lower461] using h

theorem space2049_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [163, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(163, 230), (68, 68), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    det281 det275 inv275
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2049_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2049_orbit
  simpa only [lower461] using h

theorem space2050_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [164, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(164, 162), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2050_lower : 18 ≤ frozenWangTable.L0 (spanCodes [164, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2050_orbit
  simpa only [lower461] using h

theorem space2051_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [165, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(165, 230), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    det169 det165 inv165
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2051_lower : 18 ≤ frozenWangTable.L0 (spanCodes [165, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2051_orbit
  simpa only [lower461] using h

theorem space2052_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [166, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(166, 162), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2052_lower : 18 ≤ frozenWangTable.L0 (spanCodes [166, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2052_orbit
  simpa only [lower461] using h

theorem space2053_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [167, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(167, 230), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    det185 det421 inv421
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2053_lower : 18 ≤ frozenWangTable.L0 (spanCodes [167, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2053_orbit
  simpa only [lower461] using h

theorem space2054_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [176, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(176, 68), (68, 168), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    det266 det270 inv270
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2054_lower : 18 ≤ frozenWangTable.L0 (spanCodes [176, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2054_orbit
  simpa only [lower461] using h

theorem space2055_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [177, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(177, 230), (68, 168), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    det267 det286 inv286
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2055_lower : 18 ≤ frozenWangTable.L0 (spanCodes [177, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2055_orbit
  simpa only [lower461] using h

theorem space2056_orbit :
    frozenWangTable.OrbitImage 462 (spanCodes [178, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 462 [(178, 78), (68, 184), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis462]; decide +kernel)
    (by rw [basis462]; decide +kernel)

theorem space2056_lower : 18 ≤ frozenWangTable.L0 (spanCodes [178, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 462 space2056_orbit
  simpa only [lower462] using h

theorem space2057_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [179, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(179, 179), (68, 68), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space2057_lower : 18 ≤ frozenWangTable.L0 (spanCodes [179, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space2057_orbit
  simpa only [lower463] using h

theorem space2058_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [180, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(180, 180), (68, 68), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2058_lower : 18 ≤ frozenWangTable.L0 (spanCodes [180, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2058_orbit
  simpa only [lower464] using h

theorem space2059_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [181, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(181, 250), (68, 68), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    det281 det275 inv275
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2059_lower : 18 ≤ frozenWangTable.L0 (spanCodes [181, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2059_orbit
  simpa only [lower464] using h

theorem space2060_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [182, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(182, 180), (68, 78), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2060_lower : 18 ≤ frozenWangTable.L0 (spanCodes [182, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2060_orbit
  simpa only [lower464] using h

theorem space2061_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [183, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(183, 250), (68, 78), (10, 10)]
    (codeMat 409) (codeMat 311) (codeMat 307) false
    det409 det311 inv311
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2061_lower : 18 ≤ frozenWangTable.L0 (spanCodes [183, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2061_orbit
  simpa only [lower464] using h

theorem space2062_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [258, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(258, 20), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2062_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2062_orbit
  simpa only [lower453] using h

theorem space2063_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [259, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(259, 30), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    det169 det165 inv165
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2063_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2063_orbit
  simpa only [lower453] using h

theorem space2064_orbit :
    frozenWangTable.OrbitImage 450 (spanCodes [261, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 450 [(261, 19), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    det161 det161 inv161
    (by rw [basis450]; decide +kernel)
    (by rw [basis450]; decide +kernel)

theorem space2064_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 450 space2064_orbit
  simpa only [lower450] using h

theorem space2065_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [262, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(262, 20), (68, 10), (10, 78)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    det417 det177 inv177
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2065_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2065_orbit
  simpa only [lower453] using h

theorem space2066_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [263, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(263, 30), (68, 10), (10, 78)]
    (codeMat 425) (codeMat 183) (codeMat 419) false
    det425 det183 inv183
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2066_lower : 18 ≤ frozenWangTable.L0 (spanCodes [263, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2066_orbit
  simpa only [lower453] using h

theorem space2067_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [272, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(272, 68), (68, 162), (10, 168)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    det142 det394 inv394
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2067_lower : 18 ≤ frozenWangTable.L0 (spanCodes [272, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2067_orbit
  simpa only [lower461] using h

theorem space2068_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [273, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(273, 230), (68, 162), (10, 168)]
    (codeMat 143) (codeMat 426) (codeMat 335) false
    det143 det426 inv426
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2068_lower : 18 ≤ frozenWangTable.L0 (spanCodes [273, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2068_orbit
  simpa only [lower461] using h

theorem space2069_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [274, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(274, 180), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2069_lower : 18 ≤ frozenWangTable.L0 (spanCodes [274, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2069_orbit
  simpa only [lower464] using h

theorem space2070_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [275, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(275, 250), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    det185 det421 inv421
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2070_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2070_orbit
  simpa only [lower464] using h

theorem space2071_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [276, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(276, 180), (68, 68), (10, 78)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    det305 det401 inv401
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2071_lower : 18 ≤ frozenWangTable.L0 (spanCodes [276, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2071_orbit
  simpa only [lower464] using h

theorem space2072_orbit :
    frozenWangTable.OrbitImage 464 (spanCodes [277, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 464 [(277, 250), (68, 68), (10, 78)]
    (codeMat 313) (codeMat 403) (codeMat 403) false
    det313 det403 inv403
    (by rw [basis464]; decide +kernel)
    (by rw [basis464]; decide +kernel)

theorem space2072_lower : 18 ≤ frozenWangTable.L0 (spanCodes [277, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 464 space2072_orbit
  simpa only [lower464] using h

theorem space2073_orbit :
    frozenWangTable.OrbitImage 462 (spanCodes [278, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 462 [(278, 78), (68, 178), (10, 184)]
    (codeMat 142) (codeMat 442) (codeMat 334) false
    det142 det442 inv442
    (by rw [basis462]; decide +kernel)
    (by rw [basis462]; decide +kernel)

theorem space2073_lower : 18 ≤ frozenWangTable.L0 (spanCodes [278, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 462 space2073_orbit
  simpa only [lower462] using h

theorem space2074_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [279, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(279, 179), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space2074_lower : 18 ≤ frozenWangTable.L0 (spanCodes [279, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space2074_orbit
  simpa only [lower463] using h

theorem space2075_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [289, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(289, 10), (68, 129), (10, 149)]
    (codeMat 305) (codeMat 142) (codeMat 354) false
    det305 det142 inv142
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2075_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2075_orbit
  simpa only [lower455] using h

theorem space2076_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [290, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(290, 30), (68, 129), (10, 149)]
    (codeMat 377) (codeMat 174) (codeMat 359) false
    det377 det174 inv174
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2076_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2076_orbit
  simpa only [lower455] using h

theorem space2077_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [293, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(293, 10), (68, 129), (10, 149)]
    (codeMat 313) (codeMat 158) (codeMat 358) false
    det313 det158 inv158
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2077_lower : 18 ≤ frozenWangTable.L0 (spanCodes [293, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2077_orbit
  simpa only [lower455] using h

theorem space2078_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [295, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(295, 30), (68, 129), (10, 149)]
    (codeMat 369) (codeMat 190) (codeMat 355) false
    det369 det190 inv190
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2078_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2078_orbit
  simpa only [lower455] using h

theorem space2079_orbit :
    frozenWangTable.OrbitImage 465 (spanCodes [304, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 465 [(304, 304), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    det177 det417 inv417
    (by rw [basis465]; decide +kernel)
    (by rw [basis465]; decide +kernel)

theorem space2079_lower : 18 ≤ frozenWangTable.L0 (spanCodes [304, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 465 space2079_orbit
  simpa only [lower465] using h


end QiushiMatmul.FrozenWang
