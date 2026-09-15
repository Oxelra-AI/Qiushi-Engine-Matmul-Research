import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2272_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [164, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(164, 164), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2272_lower : 18 ≤ frozenWangTable.L0 (spanCodes [164, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2272_orbit
  simpa only [lower468] using h

theorem space2273_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [165, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(165, 174), (84, 84), (10, 10)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    det337 det277 inv277
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2273_lower : 18 ≤ frozenWangTable.L0 (spanCodes [165, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2273_orbit
  simpa only [lower468] using h

theorem space2274_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [166, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(166, 164), (84, 94), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2274_lower : 18 ≤ frozenWangTable.L0 (spanCodes [166, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2274_orbit
  simpa only [lower468] using h

theorem space2275_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [167, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(167, 174), (84, 94), (10, 10)]
    (codeMat 465) (codeMat 309) (codeMat 309) false
    det465 det309 inv309
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2275_lower : 18 ≤ frozenWangTable.L0 (spanCodes [167, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2275_orbit
  simpa only [lower468] using h

theorem space2276_orbit :
    frozenWangTable.OrbitImage 461 (spanCodes [176, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 461 [(176, 68), (84, 236), (10, 10)]
    (codeMat 282) (codeMat 271) (codeMat 314) false
    det282 det271 inv271
    (by rw [basis461]; decide +kernel)
    (by rw [basis461]; decide +kernel)

theorem space2276_lower : 18 ≤ frozenWangTable.L0 (spanCodes [176, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 461 space2276_orbit
  simpa only [lower461] using h

theorem space2277_orbit :
    frozenWangTable.OrbitImage 467 (spanCodes [177, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 467 [(177, 84), (84, 169), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    det266 det270 inv270
    (by rw [basis467]; decide +kernel)
    (by rw [basis467]; decide +kernel)

theorem space2277_lower : 18 ≤ frozenWangTable.L0 (spanCodes [177, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 467 space2277_orbit
  simpa only [lower467] using h

theorem space2278_orbit :
    frozenWangTable.OrbitImage 463 (spanCodes [178, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 463 [(178, 78), (84, 185), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    det266 det302 inv302
    (by rw [basis463]; decide +kernel)
    (by rw [basis463]; decide +kernel)

theorem space2278_lower : 18 ≤ frozenWangTable.L0 (spanCodes [178, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 463 space2278_orbit
  simpa only [lower463] using h

theorem space2279_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [180, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(180, 240), (84, 84), (10, 10)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    det409 det307 inv307
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2279_lower : 18 ≤ frozenWangTable.L0 (spanCodes [180, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2279_orbit
  simpa only [lower468] using h

theorem space2280_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [181, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(181, 250), (84, 84), (10, 10)]
    (codeMat 473) (codeMat 311) (codeMat 307) false
    det473 det311 inv311
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2280_lower : 18 ≤ frozenWangTable.L0 (spanCodes [181, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2280_orbit
  simpa only [lower468] using h

theorem space2281_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [182, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(182, 240), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2281_lower : 18 ≤ frozenWangTable.L0 (spanCodes [182, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2281_orbit
  simpa only [lower468] using h

theorem space2282_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [183, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(183, 250), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    det345 det275 inv275
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2282_lower : 18 ≤ frozenWangTable.L0 (spanCodes [183, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2282_orbit
  simpa only [lower468] using h

theorem space2283_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [257, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(257, 164), (84, 174), (10, 240)]
    (codeMat 87) (codeMat 346) (codeMat 459) false
    det87 det346 inv346
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2283_lower : 18 ≤ frozenWangTable.L0 (spanCodes [257, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2283_orbit
  simpa only [lower468] using h

theorem space2284_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [258, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(258, 264), (84, 84), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    det98 det140 inv140
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2284_lower : 18 ≤ frozenWangTable.L0 (spanCodes [258, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2284_orbit
  simpa only [lower469] using h

theorem space2285_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [259, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(259, 259), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2285_lower : 18 ≤ frozenWangTable.L0 (spanCodes [259, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2285_orbit
  simpa only [lower470] using h

theorem space2286_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [261, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(261, 164), (84, 94), (10, 240)]
    (codeMat 95) (codeMat 458) (codeMat 458) false
    det95 det458 inv458
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2286_lower : 18 ≤ frozenWangTable.L0 (spanCodes [261, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2286_orbit
  simpa only [lower468] using h

theorem space2287_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [262, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(262, 259), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    det345 det275 inv275
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2287_lower : 18 ≤ frozenWangTable.L0 (spanCodes [262, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2287_orbit
  simpa only [lower470] using h

theorem space2288_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [263, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(263, 264), (84, 342), (10, 258)]
    (codeMat 107) (codeMat 156) (codeMat 102) false
    det107 det156 inv156
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2288_lower : 18 ≤ frozenWangTable.L0 (spanCodes [263, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2288_orbit
  simpa only [lower469] using h

theorem space2289_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [272, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(272, 10), (84, 174), (10, 240)]
    (codeMat 86) (codeMat 122) (codeMat 460) false
    det86 det122 inv122
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2289_lower : 18 ≤ frozenWangTable.L0 (spanCodes [272, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2289_orbit
  simpa only [lower468] using h

theorem space2290_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [274, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(274, 343), (84, 84), (10, 10)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    det337 det277 inv277
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2290_lower : 18 ≤ frozenWangTable.L0 (spanCodes [274, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2290_orbit
  simpa only [lower470] using h

theorem space2291_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [275, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(275, 348), (84, 84), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    det106 det172 inv172
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2291_lower : 18 ≤ frozenWangTable.L0 (spanCodes [275, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2291_orbit
  simpa only [lower469] using h

theorem space2292_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [277, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(277, 250), (84, 94), (10, 240)]
    (codeMat 94) (codeMat 234) (codeMat 461) false
    det94 det234 inv234
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2292_lower : 18 ≤ frozenWangTable.L0 (spanCodes [277, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2292_orbit
  simpa only [lower468] using h

theorem space2293_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [278, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(278, 349), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2293_lower : 18 ≤ frozenWangTable.L0 (spanCodes [278, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2293_orbit
  simpa only [lower470] using h

theorem space2294_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [279, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(279, 94), (84, 342), (10, 258)]
    (codeMat 99) (codeMat 188) (codeMat 103) false
    det99 det188 inv188
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2294_lower : 18 ≤ frozenWangTable.L0 (spanCodes [279, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2294_orbit
  simpa only [lower469] using h

theorem space2295_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [289, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(289, 289), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2295_lower : 18 ≤ frozenWangTable.L0 (spanCodes [289, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2295_orbit
  simpa only [lower471] using h

theorem space2296_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [290, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(290, 10), (84, 380), (10, 296)]
    (codeMat 206) (codeMat 98) (codeMat 140) false
    det206 det98 inv98
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2296_lower : 18 ≤ frozenWangTable.L0 (spanCodes [290, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2296_orbit
  simpa only [lower472] using h

theorem space2297_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [291, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(291, 10), (84, 84), (10, 296)]
    (codeMat 142) (codeMat 226) (codeMat 141) false
    det142 det226 inv226
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2297_lower : 18 ≤ frozenWangTable.L0 (spanCodes [291, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2297_orbit
  simpa only [lower472] using h

theorem space2298_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [293, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(293, 293), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space2298_lower : 18 ≤ frozenWangTable.L0 (spanCodes [293, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space2298_orbit
  simpa only [lower473] using h

theorem space2299_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [294, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(294, 294), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2299_lower : 18 ≤ frozenWangTable.L0 (spanCodes [294, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2299_orbit
  simpa only [lower474] using h

theorem space2300_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [295, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(295, 294), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    det345 det275 inv275
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2300_lower : 18 ≤ frozenWangTable.L0 (spanCodes [295, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2300_orbit
  simpa only [lower474] using h

theorem space2301_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [304, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(304, 374), (84, 84), (10, 296)]
    (codeMat 143) (codeMat 482) (codeMat 143) false
    det143 det482 inv482
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2301_lower : 18 ≤ frozenWangTable.L0 (spanCodes [304, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2301_orbit
  simpa only [lower472] using h

theorem space2302_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [305, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(305, 94), (84, 380), (10, 296)]
    (codeMat 207) (codeMat 354) (codeMat 142) false
    det207 det354 inv354
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2302_lower : 18 ≤ frozenWangTable.L0 (spanCodes [305, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2302_orbit
  simpa only [lower472] using h

theorem space2303_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [306, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(306, 373), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2303_lower : 18 ≤ frozenWangTable.L0 (spanCodes [306, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2303_orbit
  simpa only [lower471] using h


end QiushiMatmul.FrozenWang
