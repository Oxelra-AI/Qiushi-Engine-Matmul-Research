import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2016_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 68), (64, 1), (33, 80), (16, 32), (8, 8), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    det84 det161 inv161
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2016_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space2016_orbit
  simpa only [lower3] using h

theorem space2017_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 65, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 326), (129, 324), (65, 325), (33, 368), (16, 32), (8, 40), (4, 384), (2, 256)]
    (codeMat 84) (codeMat 481) (codeMat 185) false
    det84 det481 inv481
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2017_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space2017_orbit
  simpa only [lower3] using h

theorem space2018_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 197), (129, 199), (64, 3), (32, 40), (17, 248), (9, 216), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 415) (codeMat 253) false
    det84 det415 inv415
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2018_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2018_orbit
  simpa only [lower3] using h

theorem space2019_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    det84 det351 inv351
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2019_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2019_orbit
  simpa only [lower3] using h

theorem space2020_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (128, 3), (65, 455), (32, 8), (17, 472), (9, 504), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    det84 det95 inv95
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2020_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2020_orbit
  simpa only [lower3] using h

theorem space2021_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 64, 32, 17, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 1), (129, 199), (64, 3), (32, 8), (17, 248), (9, 216), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 159) (codeMat 230) false
    det84 det159 inv159
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2021_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 32, 17, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 3 space2021_orbit
  simpa only [lower3] using h

theorem space2022_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [256, 129, 65, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(256, 2), (129, 324), (65, 325), (33, 336), (16, 32), (8, 40), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 225) (codeMat 169) false
    det84 det225 inv225
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2022_lower : 9 ≤ frozenWangTable.L0 (spanCodes [256, 129, 65, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space2022_orbit
  simpa only [lower3] using h

theorem space2023_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 33, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 70), (129, 68), (64, 1), (33, 112), (16, 32), (8, 8), (4, 384), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    det84 det417 inv417
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2023_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space2023_orbit
  simpa only [lower3] using h

theorem space2024_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 326), (130, 325), (64, 2), (34, 368), (16, 40), (10, 336), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    det84 det426 inv426
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2024_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2024_orbit
  simpa only [lower3] using h

theorem space2025_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 66, 32, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 324), (130, 325), (66, 326), (32, 32), (16, 40), (10, 368), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 458) (codeMat 458) false
    det84 det458 inv458
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2025_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2025_orbit
  simpa only [lower3] using h

theorem space2026_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    det84 det266 inv266
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2026_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2026_orbit
  simpa only [lower3] using h

theorem space2027_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(260, 455), (128, 2), (68, 452), (36, 504), (20, 464), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    det84 det372 inv372
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space2027_lower : 9 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space2027_orbit
  simpa only [lower3] using h

theorem space2028_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [68, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(68, 68), (21, 30), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    det281 det275 inv275
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2028_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2028_orbit
  simpa only [lower453] using h

theorem space2029_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [68, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(68, 78), (22, 20), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    det401 det305 inv305
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2029_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2029_orbit
  simpa only [lower453] using h

theorem space2030_orbit :
    frozenWangTable.OrbitImage 453 (spanCodes [68, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 453 [(68, 78), (23, 30), (10, 10)]
    (codeMat 409) (codeMat 311) (codeMat 307) false
    det409 det311 inv311
    (by rw [basis453]; decide +kernel)
    (by rw [basis453]; decide +kernel)

theorem space2030_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 453 space2030_orbit
  simpa only [lower453] using h

theorem space2031_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 129), (33, 10), (10, 20)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    det273 det140 inv140
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2031_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2031_orbit
  simpa only [lower455] using h

theorem space2032_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 35, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 129), (35, 30), (10, 20)]
    (codeMat 337) (codeMat 172) (codeMat 99) false
    det337 det172 inv172
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2032_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 35, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2032_orbit
  simpa only [lower455] using h

theorem space2033_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 37, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 129), (37, 10), (10, 20)]
    (codeMat 281) (codeMat 156) (codeMat 102) false
    det281 det156 inv156
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2033_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 37, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2033_orbit
  simpa only [lower455] using h

theorem space2034_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 38, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 129), (38, 30), (10, 20)]
    (codeMat 345) (codeMat 188) (codeMat 103) false
    det345 det188 inv188
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2034_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 38, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2034_orbit
  simpa only [lower455] using h

theorem space2035_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 49, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 149), (49, 10), (10, 20)]
    (codeMat 401) (codeMat 396) (codeMat 106) false
    det401 det396 inv396
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2035_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 49, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2035_orbit
  simpa only [lower455] using h

theorem space2036_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 149), (51, 30), (10, 20)]
    (codeMat 465) (codeMat 428) (codeMat 107) false
    det465 det428 inv428
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2036_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2036_orbit
  simpa only [lower455] using h

theorem space2037_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 52, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 149), (52, 30), (10, 20)]
    (codeMat 473) (codeMat 412) (codeMat 111) false
    det473 det412 inv412
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2037_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 52, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2037_orbit
  simpa only [lower455] using h

theorem space2038_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [68, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(68, 149), (55, 10), (10, 20)]
    (codeMat 409) (codeMat 444) (codeMat 110) false
    det409 det444 inv444
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2038_lower : 18 ≤ frozenWangTable.L0 (spanCodes [68, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2038_orbit
  simpa only [lower455] using h

theorem space2039_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [129, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(129, 10), (68, 20), (10, 129)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    det161 det266 inv266
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2039_lower : 18 ≤ frozenWangTable.L0 (spanCodes [129, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2039_orbit
  simpa only [lower455] using h

theorem space2040_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [131, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(131, 10), (68, 20), (10, 129)]
    (codeMat 169) (codeMat 298) (codeMat 270) false
    det169 det298 inv298
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2040_lower : 18 ≤ frozenWangTable.L0 (spanCodes [131, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2040_orbit
  simpa only [lower455] using h

theorem space2041_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [133, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(133, 30), (68, 20), (10, 129)]
    (codeMat 225) (codeMat 282) (codeMat 267) false
    det225 det282 inv282
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2041_lower : 18 ≤ frozenWangTable.L0 (spanCodes [133, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2041_orbit
  simpa only [lower455] using h

theorem space2042_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [134, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(134, 30), (68, 20), (10, 129)]
    (codeMat 233) (codeMat 314) (codeMat 271) false
    det233 det314 inv314
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2042_lower : 18 ≤ frozenWangTable.L0 (spanCodes [134, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2042_orbit
  simpa only [lower455] using h

theorem space2043_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [145, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(145, 10), (68, 149), (10, 129)]
    (codeMat 177) (codeMat 270) (codeMat 298) false
    det177 det270 inv270
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2043_lower : 18 ≤ frozenWangTable.L0 (spanCodes [145, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2043_orbit
  simpa only [lower455] using h

theorem space2044_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [147, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(147, 10), (68, 149), (10, 129)]
    (codeMat 185) (codeMat 302) (codeMat 302) false
    det185 det302 inv302
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2044_lower : 18 ≤ frozenWangTable.L0 (spanCodes [147, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2044_orbit
  simpa only [lower455] using h

theorem space2045_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [148, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(148, 30), (68, 149), (10, 129)]
    (codeMat 249) (codeMat 286) (codeMat 303) false
    det249 det286 inv286
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2045_lower : 18 ≤ frozenWangTable.L0 (spanCodes [148, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2045_orbit
  simpa only [lower455] using h

theorem space2046_orbit :
    frozenWangTable.OrbitImage 455 (spanCodes [151, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 455 [(151, 30), (68, 149), (10, 129)]
    (codeMat 241) (codeMat 318) (codeMat 299) false
    det241 det318 inv318
    (by rw [basis455]; decide +kernel)
    (by rw [basis455]; decide +kernel)

theorem space2046_lower : 18 ≤ frozenWangTable.L0 (spanCodes [151, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 455 space2046_orbit
  simpa only [lower455] using h

theorem space2047_orbit :
    frozenWangTable.OrbitImage 459 (spanCodes [160, 68, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 459 [(160, 10), (68, 68), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis459]; decide +kernel)
    (by rw [basis459]; decide +kernel)

theorem space2047_lower : 18 ≤ frozenWangTable.L0 (spanCodes [160, 68, 10]) := by
  have h := frozenWangTable.lower_le_L0 459 space2047_orbit
  simpa only [lower459] using h


end QiushiMatmul.FrozenWang
