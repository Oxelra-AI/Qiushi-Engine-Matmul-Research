import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3008_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 68, 36, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (128, 128), (68, 150), (36, 3), (21, 224), (10, 255)]
    (codeMat 103) (codeMat 205) (codeMat 242) true
    det103 det205 inv205
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3008_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 36, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3008_orbit
  simpa only [lower35] using h

theorem space3009_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [256, 128, 66, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(256, 2), (128, 1), (66, 70), (34, 80), (16, 8), (10, 112)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    det84 det106 inv106
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3009_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 31 space3009_orbit
  simpa only [lower31] using h

theorem space3010_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 64, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    det84 det266 inv266
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space3010_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 31 space3010_orbit
  simpa only [lower31] using h

theorem space3011_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 135, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 28), (135, 252), (71, 255), (39, 20), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 249) (codeMat 425) true
    det95 det249 inv249
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3011_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 135, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3011_orbit
  simpa only [lower35] using h

theorem space3012_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 135, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 232), (135, 96), (71, 224), (39, 150), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 491) (codeMat 375) false
    det299 det491 inv491
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3012_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3012_orbit
  simpa only [lower35] using h

theorem space3013_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 135, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 96), (135, 105), (68, 104), (36, 128), (17, 150), (10, 148)]
    (codeMat 93) (codeMat 474) (codeMat 395) true
    det93 det474 inv474
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3013_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 135, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3013_orbit
  simpa only [lower35] using h

theorem space3014_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [259, 134, 66, 34, 20, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(259, 78), (134, 436), (66, 507), (34, 160), (20, 176), (10, 480)]
    (codeMat 157) (codeMat 425) (codeMat 249) false
    det157 det425 inv425
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3014_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 134, 66, 34, 20, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3014_orbit
  simpa only [lower65] using h

theorem space3015_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 150, 66, 34, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 227), (150, 28), (66, 105), (34, 224), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 165) (codeMat 163) false
    det143 det165 inv165
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3015_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 150, 66, 34, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3015_orbit
  simpa only [lower35] using h

theorem space3016_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 132, 64, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 2), (132, 20), (64, 128), (32, 1), (16, 8), (10, 96)]
    (codeMat 98) (codeMat 84) (codeMat 84) true
    det98 det84 inv84
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3016_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 132, 64, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3016_orbit
  simpa only [lower35] using h

theorem space3017_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 130, 65, 33, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 104), (130, 1), (65, 9), (33, 252), (16, 3), (10, 31)]
    (codeMat 125) (codeMat 299) (codeMat 318) true
    det125 det299 inv299
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3017_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 130, 65, 33, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3017_orbit
  simpa only [lower35] using h

theorem space3018_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 128, 67, 35, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 252), (128, 130), (67, 139), (35, 104), (18, 128), (10, 136)]
    (codeMat 215) (codeMat 281) (codeMat 281) false
    det215 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3018_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 128, 67, 35, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3018_orbit
  simpa only [lower35] using h

theorem space3019_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 144, 67, 35, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 246), (144, 128), (67, 232), (35, 252), (10, 224), (5, 3)]
    (codeMat 183) (codeMat 172) (codeMat 99) true
    det183 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3019_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 144, 67, 35, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space3019_orbit
  simpa only [lower35] using h

theorem space3020_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [273, 146, 81, 49, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(273, 95), (146, 27), (81, 287), (49, 79), (10, 507), (6, 1)]
    (codeMat 305) (codeMat 123) (codeMat 236) false
    det305 det123 inv123
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3020_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 146, 81, 49, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 65 space3020_orbit
  simpa only [lower65] using h

theorem space3021_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 133, 71, 39, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 252), (133, 139), (71, 126), (39, 104), (21, 136), (10, 232)]
    (codeMat 214) (codeMat 346) (codeMat 459) false
    det214 det346 inv346
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3021_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 133, 71, 39, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3021_orbit
  simpa only [lower35] using h

theorem space3022_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 66, 34, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 96), (128, 8), (66, 97), (34, 224), (21, 28), (10, 227)]
    (codeMat 116) (codeMat 337) (codeMat 337) true
    det116 det337 inv337
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3022_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 66, 34, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3022_orbit
  simpa only [lower35] using h

theorem space3023_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 129, 71, 39, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 252), (129, 227), (71, 255), (39, 104), (17, 97), (10, 105)]
    (codeMat 115) (codeMat 491) (codeMat 375) true
    det115 det491 inv491
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3023_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 71, 39, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3023_orbit
  simpa only [lower35] using h

theorem space3024_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 71, 39, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 126), (128, 9), (71, 252), (39, 232), (16, 8), (10, 104)]
    (codeMat 214) (codeMat 354) (codeMat 142) false
    det214 det354 inv354
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3024_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 71, 39, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3024_orbit
  simpa only [lower35] using h

theorem space3025_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [260, 130, 67, 35, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(260, 128), (130, 2), (67, 22), (35, 224), (16, 3), (10, 31)]
    (codeMat 111) (codeMat 267) (codeMat 282) true
    det111 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3025_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 130, 67, 35, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3025_orbit
  simpa only [lower35] using h

theorem space3026_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 129, 83, 51, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 118), (129, 255), (83, 28), (51, 136), (10, 224), (5, 128)]
    (codeMat 94) (codeMat 498) (codeMat 206) false
    det94 det498 inv498
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3026_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 129, 83, 51, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space3026_orbit
  simpa only [lower35] using h

theorem space3027_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 145, 67, 35, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 232), (145, 139), (67, 245), (35, 227), (10, 252), (5, 3)]
    (codeMat 183) (codeMat 185) (codeMat 481) true
    det183 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3027_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 145, 67, 35, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space3027_orbit
  simpa only [lower35] using h

theorem space3028_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 145, 66, 34, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 97), (145, 28), (66, 227), (34, 96), (10, 224), (4, 8)]
    (codeMat 142) (codeMat 141) (codeMat 226) false
    det142 det141 inv141
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3028_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 145, 66, 34, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3028_orbit
  simpa only [lower35] using h

theorem space3029_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 148, 66, 34, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 227), (148, 28), (66, 97), (34, 224), (10, 96), (1, 8)]
    (codeMat 142) (codeMat 165) (codeMat 163) false
    det142 det165 inv165
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3029_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 148, 66, 34, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3029_orbit
  simpa only [lower35] using h

theorem space3030_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 178, 96, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 126), (178, 252), (96, 20), (10, 104), (4, 9), (1, 8)]
    (codeMat 177) (codeMat 188) (codeMat 103) true
    det177 det188 inv188
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3030_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 178, 96, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3030_orbit
  simpa only [lower35] using h

theorem space3031_orbit :
    frozenWangTable.OrbitImage 190 (spanCodes [260, 149, 71, 39, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 190 [(260, 128), (149, 463), (71, 484), (39, 367), (10, 366)]
    (codeMat 379) (codeMat 185) (codeMat 481) false
    det379 det185 inv185
    (by rw [basis190]; decide +kernel)
    (by rw [basis190]; decide +kernel)

theorem space3031_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 149, 71, 39, 10]) := by
  have h := frozenWangTable.lower_le_L0 190 space3031_orbit
  simpa only [lower190] using h

theorem space3032_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 67, 35, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 9), (131, 104), (67, 96), (35, 31), (22, 252), (10, 224)]
    (codeMat 124) (codeMat 244) (codeMat 95) true
    det124 det244 inv244
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3032_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 67, 35, 22, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3032_orbit
  simpa only [lower35] using h

theorem space3033_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 132, 71, 39, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 150), (132, 148), (71, 151), (39, 232), (23, 104), (10, 224)]
    (codeMat 157) (codeMat 489) (codeMat 241) false
    det157 det489 inv489
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3033_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 132, 71, 39, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3033_orbit
  simpa only [lower35] using h

theorem space3034_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [257, 130, 64, 32, 21, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(257, 245), (130, 260), (64, 27), (32, 320), (21, 176), (10, 480)]
    (codeMat 159) (codeMat 397) (codeMat 250) false
    det159 det397 inv397
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3034_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 130, 64, 32, 21, 10]) := by
  have h := frozenWangTable.lower_le_L0 65 space3034_orbit
  simpa only [lower65] using h

theorem space3035_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 128, 70, 38, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 3), (128, 1), (70, 148), (38, 136), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 102) (codeMat 156) false
    det212 det102 inv102
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3035_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 70, 38, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3035_orbit
  simpa only [lower35] using h

theorem space3036_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [261, 130, 65, 33, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(261, 96), (130, 1), (65, 8), (33, 224), (16, 3), (10, 28)]
    (codeMat 125) (codeMat 266) (codeMat 266) true
    det125 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3036_lower : 15 ≤ frozenWangTable.L0 (spanCodes [261, 130, 65, 33, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space3036_orbit
  simpa only [lower35] using h

theorem space3037_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [288, 135, 96, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(288, 27), (135, 272), (96, 283), (17, 78), (10, 79)]
    (codeMat 299) (codeMat 253) (codeMat 415) false
    det299 det253 inv253
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space3037_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 135, 96, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 149 space3037_orbit
  simpa only [lower149] using h

theorem space3038_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [259, 178, 96, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(259, 208), (178, 228), (96, 363), (10, 398), (7, 16)]
    (codeMat 334) (codeMat 254) (codeMat 443) false
    det334 det254 inv254
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space3038_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 178, 96, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space3038_orbit
  simpa only [lower220] using h

theorem space3039_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [274, 129, 66, 34, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(274, 78), (129, 255), (66, 228), (34, 496), (10, 480), (7, 320)]
    (codeMat 87) (codeMat 498) (codeMat 206) false
    det87 det498 inv498
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space3039_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 129, 66, 34, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 65 space3039_orbit
  simpa only [lower65] using h


end QiushiMatmul.FrozenWang
