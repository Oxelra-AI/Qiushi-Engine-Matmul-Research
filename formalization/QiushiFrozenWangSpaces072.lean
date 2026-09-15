import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2304_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [308, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(308, 376), (84, 84), (10, 10)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    det337 det277 inv277
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2304_lower : 18 ≤ frozenWangTable.L0 (spanCodes [308, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2304_orbit
  simpa only [lower474] using h

theorem space2305_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [309, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(309, 370), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2305_lower : 18 ≤ frozenWangTable.L0 (spanCodes [309, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2305_orbit
  simpa only [lower474] using h

theorem space2306_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [311, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(311, 369), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    det281 det279 inv279
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space2306_lower : 18 ≤ frozenWangTable.L0 (spanCodes [311, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space2306_orbit
  simpa only [lower473] using h

theorem space2307_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [385, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(385, 289), (84, 94), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2307_lower : 18 ≤ frozenWangTable.L0 (spanCodes [385, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2307_orbit
  simpa only [lower471] using h

theorem space2308_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [386, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(386, 10), (84, 84), (10, 296)]
    (codeMat 204) (codeMat 102) (codeMat 156) false
    det204 det102 inv102
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2308_lower : 18 ≤ frozenWangTable.L0 (spanCodes [386, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2308_orbit
  simpa only [lower472] using h

theorem space2309_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [387, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(387, 10), (84, 380), (10, 296)]
    (codeMat 140) (codeMat 486) (codeMat 157) false
    det140 det486 inv486
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2309_lower : 18 ≤ frozenWangTable.L0 (spanCodes [387, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2309_orbit
  simpa only [lower472] using h

theorem space2310_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [388, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(388, 294), (84, 94), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2310_lower : 18 ≤ frozenWangTable.L0 (spanCodes [388, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2310_orbit
  simpa only [lower474] using h

theorem space2311_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [389, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(389, 294), (84, 84), (10, 10)]
    (codeMat 473) (codeMat 311) (codeMat 307) false
    det473 det311 inv311
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2311_lower : 18 ≤ frozenWangTable.L0 (spanCodes [389, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2311_orbit
  simpa only [lower474] using h

theorem space2312_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [391, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(391, 293), (84, 94), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space2312_lower : 18 ≤ frozenWangTable.L0 (spanCodes [391, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space2312_orbit
  simpa only [lower473] using h

theorem space2313_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [400, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(400, 374), (84, 380), (10, 296)]
    (codeMat 141) (codeMat 230) (codeMat 159) false
    det141 det230 inv230
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2313_lower : 18 ≤ frozenWangTable.L0 (spanCodes [400, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2313_orbit
  simpa only [lower472] using h

theorem space2314_orbit :
    frozenWangTable.OrbitImage 472 (spanCodes [401, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 472 [(401, 94), (84, 84), (10, 296)]
    (codeMat 205) (codeMat 358) (codeMat 158) false
    det205 det358 inv358
    (by rw [basis472]; decide +kernel)
    (by rw [basis472]; decide +kernel)

theorem space2314_lower : 18 ≤ frozenWangTable.L0 (spanCodes [401, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 472 space2314_orbit
  simpa only [lower472] using h

theorem space2315_orbit :
    frozenWangTable.OrbitImage 471 (spanCodes [402, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 471 [(402, 373), (84, 84), (10, 10)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    det409 det307 inv307
    (by rw [basis471]; decide +kernel)
    (by rw [basis471]; decide +kernel)

theorem space2315_lower : 18 ≤ frozenWangTable.L0 (spanCodes [402, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 471 space2315_orbit
  simpa only [lower471] using h

theorem space2316_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [405, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(405, 369), (84, 84), (10, 10)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    det409 det307 inv307
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space2316_lower : 18 ≤ frozenWangTable.L0 (spanCodes [405, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 473 space2316_orbit
  simpa only [lower473] using h

theorem space2317_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [406, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(406, 376), (84, 94), (10, 10)]
    (codeMat 465) (codeMat 309) (codeMat 309) false
    det465 det309 inv309
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2317_lower : 18 ≤ frozenWangTable.L0 (spanCodes [406, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2317_orbit
  simpa only [lower474] using h

theorem space2318_orbit :
    frozenWangTable.OrbitImage 474 (spanCodes [407, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 474 [(407, 370), (84, 84), (10, 10)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    det409 det307 inv307
    (by rw [basis474]; decide +kernel)
    (by rw [basis474]; decide +kernel)

theorem space2318_lower : 18 ≤ frozenWangTable.L0 (spanCodes [407, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 474 space2318_orbit
  simpa only [lower474] using h

theorem space2319_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [416, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(416, 10), (84, 94), (10, 240)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    det84 det94 inv94
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2319_lower : 18 ≤ frozenWangTable.L0 (spanCodes [416, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2319_orbit
  simpa only [lower468] using h

theorem space2320_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [418, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(418, 343), (84, 94), (10, 10)]
    (codeMat 465) (codeMat 309) (codeMat 309) false
    det465 det309 inv309
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2320_lower : 18 ≤ frozenWangTable.L0 (spanCodes [418, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2320_orbit
  simpa only [lower470] using h

theorem space2321_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [419, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(419, 348), (84, 342), (10, 258)]
    (codeMat 122) (codeMat 428) (codeMat 107) false
    det122 det428 inv428
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2321_lower : 18 ≤ frozenWangTable.L0 (spanCodes [419, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2321_orbit
  simpa only [lower469] using h

theorem space2322_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [420, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(420, 349), (84, 84), (10, 10)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    det409 det307 inv307
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2322_lower : 18 ≤ frozenWangTable.L0 (spanCodes [420, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2322_orbit
  simpa only [lower470] using h

theorem space2323_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [421, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(421, 94), (84, 84), (10, 258)]
    (codeMat 115) (codeMat 412) (codeMat 111) false
    det115 det412 inv412
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2323_lower : 18 ≤ frozenWangTable.L0 (spanCodes [421, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2323_orbit
  simpa only [lower469] using h

theorem space2324_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [423, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(423, 250), (84, 174), (10, 240)]
    (codeMat 92) (codeMat 494) (codeMat 501) false
    det92 det494 inv494
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2324_lower : 18 ≤ frozenWangTable.L0 (spanCodes [423, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2324_orbit
  simpa only [lower468] using h

theorem space2325_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [433, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(433, 164), (84, 94), (10, 240)]
    (codeMat 85) (codeMat 382) (codeMat 499) false
    det85 det382 inv382
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2325_lower : 18 ≤ frozenWangTable.L0 (spanCodes [433, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2325_orbit
  simpa only [lower468] using h

theorem space2326_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [434, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(434, 264), (84, 342), (10, 258)]
    (codeMat 114) (codeMat 396) (codeMat 106) false
    det114 det396 inv396
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2326_lower : 18 ≤ frozenWangTable.L0 (spanCodes [434, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2326_orbit
  simpa only [lower469] using h

theorem space2327_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [435, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(435, 259), (84, 94), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2327_lower : 18 ≤ frozenWangTable.L0 (spanCodes [435, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2327_orbit
  simpa only [lower470] using h

theorem space2328_orbit :
    frozenWangTable.OrbitImage 470 (spanCodes [436, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 470 [(436, 259), (84, 84), (10, 10)]
    (codeMat 473) (codeMat 311) (codeMat 307) false
    det473 det311 inv311
    (by rw [basis470]; decide +kernel)
    (by rw [basis470]; decide +kernel)

theorem space2328_lower : 18 ≤ frozenWangTable.L0 (spanCodes [436, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 470 space2328_orbit
  simpa only [lower470] using h

theorem space2329_orbit :
    frozenWangTable.OrbitImage 469 (spanCodes [437, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 469 [(437, 264), (84, 84), (10, 258)]
    (codeMat 123) (codeMat 444) (codeMat 110) false
    det123 det444 inv444
    (by rw [basis469]; decide +kernel)
    (by rw [basis469]; decide +kernel)

theorem space2329_lower : 18 ≤ frozenWangTable.L0 (spanCodes [437, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 469 space2329_orbit
  simpa only [lower469] using h

theorem space2330_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [439, 84, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(439, 164), (84, 174), (10, 240)]
    (codeMat 93) (codeMat 206) (codeMat 498) false
    det93 det206 inv206
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space2330_lower : 18 ≤ frozenWangTable.L0 (spanCodes [439, 84, 10]) := by
  have h := frozenWangTable.lower_le_L0 468 space2330_orbit
  simpa only [lower468] using h

theorem space2331_orbit :
    frozenWangTable.OrbitImage 429 (spanCodes [84, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 429 [(84, 98), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis429]; decide +kernel)
    (by rw [basis429]; decide +kernel)

theorem space2331_lower : 17 ≤ frozenWangTable.L0 (spanCodes [84, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 429 space2331_orbit
  simpa only [lower429] using h

theorem space2332_orbit :
    frozenWangTable.OrbitImage 429 (spanCodes [84, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 429 [(84, 115), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 279) (codeMat 279) false
    det267 det279 inv279
    (by rw [basis429]; decide +kernel)
    (by rw [basis429]; decide +kernel)

theorem space2332_lower : 17 ≤ frozenWangTable.L0 (spanCodes [84, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 429 space2332_orbit
  simpa only [lower429] using h

theorem space2333_orbit :
    frozenWangTable.OrbitImage 279 (spanCodes [68, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 279 [(68, 68), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    det273 det273 inv273
    (by rw [basis279]; decide +kernel)
    (by rw [basis279]; decide +kernel)

theorem space2333_lower : 17 ≤ frozenWangTable.L0 (spanCodes [68, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 279 space2333_orbit
  simpa only [lower279] using h

theorem space2334_orbit :
    frozenWangTable.OrbitImage 431 (spanCodes [70, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 431 [(70, 228), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 271) (codeMat 314) false
    det275 det271 inv271
    (by rw [basis431]; decide +kernel)
    (by rw [basis431]; decide +kernel)

theorem space2334_lower : 17 ≤ frozenWangTable.L0 (spanCodes [70, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 431 space2334_orbit
  simpa only [lower431] using h

theorem space2335_orbit :
    frozenWangTable.OrbitImage 439 (spanCodes [66, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 439 [(66, 21), (22, 160), (10, 20)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    det142 det305 inv305
    (by rw [basis439]; decide +kernel)
    (by rw [basis439]; decide +kernel)

theorem space2335_lower : 17 ≤ frozenWangTable.L0 (spanCodes [66, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 439 space2335_orbit
  simpa only [lower439] using h


end QiushiMatmul.FrozenWang
