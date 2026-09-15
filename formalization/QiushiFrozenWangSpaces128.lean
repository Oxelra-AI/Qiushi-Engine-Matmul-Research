import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space4096_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [160, 68, 16, 12, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(160, 104), (68, 148), (16, 8), (12, 20), (2, 1), (1, 2)]
    (codeMat 401) (codeMat 266) (codeMat 266) false
    det401 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4096_lower : 15 ≤ frozenWangTable.L0 (spanCodes [160, 68, 16, 12, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4096_orbit
  simpa only [lower35] using h

theorem space4097_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [133, 65, 37, 21, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(133, 170), (65, 438), (37, 43), (21, 42), (3, 32)]
    (codeMat 394) (codeMat 124) (codeMat 124) false
    det394 det124 inv124
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4097_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 65, 37, 21, 3]) := by
  have h := frozenWangTable.lower_le_L0 189 space4097_orbit
  simpa only [lower189] using h

theorem space4098_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [141, 73, 45, 29, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(141, 85), (73, 27), (45, 325), (29, 69), (3, 1)]
    (codeMat 177) (codeMat 313) (codeMat 313) false
    det177 det313 inv313
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4098_lower : 15 ≤ frozenWangTable.L0 (spanCodes [141, 73, 45, 29, 3]) := by
  have h := frozenWangTable.lower_le_L0 149 space4098_orbit
  simpa only [lower149] using h

theorem space4099_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [139, 72, 40, 26, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(139, 129), (72, 1), (40, 438), (26, 138), (6, 32)]
    (codeMat 334) (codeMat 311) (codeMat 307) false
    det334 det311 inv311
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4099_lower : 15 ≤ frozenWangTable.L0 (spanCodes [139, 72, 40, 26, 6]) := by
  have h := frozenWangTable.lower_le_L0 189 space4099_orbit
  simpa only [lower189] using h

theorem space4100_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [138, 73, 41, 26, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(138, 193), (73, 1), (41, 399), (26, 209), (7, 36)]
    (codeMat 375) (codeMat 309) (codeMat 309) false
    det375 det309 inv309
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4100_lower : 15 ≤ frozenWangTable.L0 (spanCodes [138, 73, 41, 26, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space4100_orbit
  simpa only [lower220] using h

theorem space4101_orbit :
    frozenWangTable.OrbitImage 190 (spanCodes [138, 72, 41, 25, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 190 [(138, 495), (72, 128), (41, 10), (25, 42), (5, 1)]
    (codeMat 401) (codeMat 190) (codeMat 355) false
    det401 det190 inv190
    (by rw [basis190]; decide +kernel)
    (by rw [basis190]; decide +kernel)

theorem space4101_lower : 15 ≤ frozenWangTable.L0 (spanCodes [138, 72, 41, 25, 5]) := by
  have h := frozenWangTable.lower_le_L0 190 space4101_orbit
  simpa only [lower190] using h

theorem space4102_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [138, 75, 41, 24, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(138, 33), (75, 11), (41, 278), (24, 32), (7, 128)]
    (codeMat 143) (codeMat 299) (codeMat 318) true
    det143 det299 inv299
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4102_lower : 15 ≤ frozenWangTable.L0 (spanCodes [138, 75, 41, 24, 7]) := by
  have h := frozenWangTable.lower_le_L0 189 space4102_orbit
  simpa only [lower189] using h

theorem space4103_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [129, 68, 33, 16, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(129, 136), (68, 232), (33, 30), (16, 2), (8, 3), (3, 8)]
    (codeMat 330) (codeMat 313) (codeMat 313) false
    det330 det313 inv313
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4103_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 68, 33, 16, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4103_orbit
  simpa only [lower35] using h

theorem space4104_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [129, 68, 32, 16, 9, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(129, 28), (68, 224), (32, 128), (16, 2), (9, 8), (2, 3)]
    (codeMat 275) (codeMat 266) (codeMat 266) true
    det275 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4104_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 68, 32, 16, 9, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4104_orbit
  simpa only [lower35] using h

theorem space4105_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [128, 68, 34, 16, 8, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(128, 128), (68, 96), (34, 20), (16, 2), (8, 1), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    det266 det273 inv273
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4105_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 68, 34, 16, 8, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4105_orbit
  simpa only [lower35] using h

theorem space4106_orbit :
    frozenWangTable.OrbitImage 72 (spanCodes [134, 68, 36, 16, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 72 [(134, 113), (68, 316), (36, 63), (16, 1), (14, 52), (1, 32)]
    (codeMat 394) (codeMat 358) (codeMat 158) false
    det394 det358 inv358
    (by rw [basis72]; decide +kernel)
    (by rw [basis72]; decide +kernel)

theorem space4106_lower : 15 ≤ frozenWangTable.L0 (spanCodes [134, 68, 36, 16, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 72 space4106_orbit
  simpa only [lower72] using h

theorem space4107_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [136, 68, 40, 16, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(136, 20), (68, 104), (40, 128), (16, 2), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 298) (codeMat 270) true
    det273 det298 inv298
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4107_lower : 15 ≤ frozenWangTable.L0 (spanCodes [136, 68, 40, 16, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4107_orbit
  simpa only [lower35] using h

theorem space4108_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [146, 80, 49, 9, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(146, 1), (80, 42), (49, 160), (9, 32), (4, 438)]
    (codeMat 215) (codeMat 302) (codeMat 302) true
    det215 det302 inv302
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4108_lower : 15 ≤ frozenWangTable.L0 (spanCodes [146, 80, 49, 9, 4]) := by
  have h := frozenWangTable.lower_le_L0 189 space4108_orbit
  simpa only [lower189] using h

theorem space4109_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [139, 65, 40, 18, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(139, 10), (65, 16), (40, 325), (18, 1), (7, 256)]
    (codeMat 107) (codeMat 302) (codeMat 302) false
    det107 det302 inv302
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4109_lower : 15 ≤ frozenWangTable.L0 (spanCodes [139, 65, 40, 18, 7]) := by
  have h := frozenWangTable.lower_le_L0 149 space4109_orbit
  simpa only [lower149] using h

theorem space4110_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [132, 70, 38, 18, 8, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(132, 232), (70, 96), (38, 30), (18, 3), (8, 9), (1, 8)]
    (codeMat 331) (codeMat 307) (codeMat 311) false
    det331 det307 inv307
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4110_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 70, 38, 18, 8, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4110_orbit
  simpa only [lower35] using h

theorem space4111_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [129, 72, 34, 26, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(129, 414), (72, 192), (34, 52), (26, 53), (6, 16)]
    (codeMat 394) (codeMat 409) (codeMat 473) false
    det394 det409 inv409
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4111_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 72, 34, 26, 6]) := by
  have h := frozenWangTable.lower_le_L0 220 space4111_orbit
  simpa only [lower220] using h

theorem space4112_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [146, 82, 49, 9, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(146, 27), (82, 11), (49, 324), (9, 1), (6, 256)]
    (codeMat 99) (codeMat 311) (codeMat 307) false
    det99 det311 inv311
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4112_lower : 15 ≤ frozenWangTable.L0 (spanCodes [146, 82, 49, 9, 6]) := by
  have h := frozenWangTable.lower_le_L0 149 space4112_orbit
  simpa only [lower149] using h

theorem space4113_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [132, 68, 37, 16, 9, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(132, 96), (68, 224), (37, 28), (16, 9), (9, 3), (2, 8)]
    (codeMat 267) (codeMat 267) (codeMat 282) false
    det267 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4113_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 68, 37, 16, 9, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4113_orbit
  simpa only [lower35] using h

theorem space4114_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [133, 68, 37, 16, 8, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(133, 227), (68, 252), (37, 139), (16, 8), (8, 9), (3, 3)]
    (codeMat 282) (codeMat 313) (codeMat 313) true
    det282 det313 inv313
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4114_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 68, 37, 16, 8, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4114_orbit
  simpa only [lower35] using h

theorem space4115_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [147, 80, 48, 11, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(147, 414), (80, 350), (48, 36), (11, 53), (4, 16)]
    (codeMat 331) (codeMat 241) (codeMat 489) false
    det331 det241 inv241
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space4115_lower : 15 ≤ frozenWangTable.L0 (spanCodes [147, 80, 48, 11, 4]) := by
  have h := frozenWangTable.lower_le_L0 220 space4115_orbit
  simpa only [lower220] using h

theorem space4116_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [132, 76, 36, 24, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(132, 96), (76, 127), (36, 128), (24, 3), (2, 8), (1, 9)]
    (codeMat 281) (codeMat 281) (codeMat 281) true
    det281 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4116_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 76, 36, 24, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space4116_orbit
  simpa only [lower35] using h

theorem space4117_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [265, 160, 72, 25, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(265, 245), (160, 150), (72, 130), (25, 97), (5, 9), (3, 8)]
    (codeMat 177) (codeMat 499) (codeMat 382) true
    det177 det499 inv499
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4117_lower : 15 ≤ frozenWangTable.L0 (spanCodes [265, 160, 72, 25, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space4117_orbit
  simpa only [lower35] using h

theorem space4118_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [264, 160, 72, 28, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(264, 129), (160, 139), (72, 128), (28, 284), (3, 32)]
    (codeMat 116) (codeMat 468) (codeMat 87) true
    det116 det468 inv468
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4118_lower : 15 ≤ frozenWangTable.L0 (spanCodes [264, 160, 72, 28, 3]) := by
  have h := frozenWangTable.lower_le_L0 189 space4118_orbit
  simpa only [lower189] using h

theorem space4119_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [258, 162, 68, 16, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(258, 506), (162, 170), (68, 79), (16, 16), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    det401 det309 inv309
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4119_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 162, 68, 16, 10, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4119_orbit
  simpa only [lower65] using h

theorem space4120_orbit :
    frozenWangTable.OrbitImage 65 (spanCodes [260, 162, 68, 16, 14, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 65 [(260, 1), (162, 69), (68, 26), (16, 320), (14, 160), (1, 16)]
    (codeMat 141) (codeMat 142) (codeMat 354) false
    det141 det142 inv142
    (by rw [basis65]; decide +kernel)
    (by rw [basis65]; decide +kernel)

theorem space4120_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 162, 68, 16, 14, 1]) := by
  have h := frozenWangTable.lower_le_L0 65 space4120_orbit
  simpa only [lower65] using h

theorem space4121_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 163, 64, 19, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 118), (163, 157), (64, 9), (19, 104), (9, 8), (7, 128)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    det95 det419 inv419
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4121_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 163, 64, 19, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 35 space4121_orbit
  simpa only [lower35] using h

theorem space4122_orbit :
    frozenWangTable.OrbitImage 189 (spanCodes [275, 163, 83, 9, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 189 [(275, 285), (163, 171), (83, 284), (9, 32), (7, 128)]
    (codeMat 92) (codeMat 342) (codeMat 215) false
    det92 det342 inv342
    (by rw [basis189]; decide +kernel)
    (by rw [basis189]; decide +kernel)

theorem space4122_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 163, 83, 9, 7]) := by
  have h := frozenWangTable.lower_le_L0 189 space4122_orbit
  simpa only [lower189] using h

theorem space4123_orbit :
    frozenWangTable.OrbitImage 149 (spanCodes [260, 163, 68, 16, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 149 [(260, 27), (163, 340), (68, 350), (16, 256), (11, 272)]
    (codeMat 158) (codeMat 236) (codeMat 123) false
    det158 det236 inv236
    (by rw [basis149]; decide +kernel)
    (by rw [basis149]; decide +kernel)

theorem space4123_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 163, 68, 16, 11]) := by
  have h := frozenWangTable.lower_le_L0 149 space4123_orbit
  simpa only [lower149] using h

theorem space4124_orbit :
    frozenWangTable.OrbitImage 190 (spanCodes [272, 146, 80, 49, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 190 [(272, 356), (146, 32), (80, 484), (49, 366), (4, 1)]
    (codeMat 313) (codeMat 141) (codeMat 226) false
    det313 det141 inv141
    (by rw [basis190]; decide +kernel)
    (by rw [basis190]; decide +kernel)

theorem space4124_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 146, 80, 49, 4]) := by
  have h := frozenWangTable.lower_le_L0 190 space4124_orbit
  simpa only [lower190] using h

theorem space4125_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [274, 144, 80, 51, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(274, 356), (144, 32), (80, 480), (51, 367), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) false
    det305 det141 inv141
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space4125_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 144, 80, 51, 4]) := by
  have h := frozenWangTable.lower_le_L0 197 space4125_orbit
  simpa only [lower197] using h

theorem space4126_orbit :
    frozenWangTable.OrbitImage 190 (spanCodes [257, 128, 83, 35, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 190 [(257, 452), (128, 1), (83, 463), (35, 160), (7, 128)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    det92 det331 inv331
    (by rw [basis190]; decide +kernel)
    (by rw [basis190]; decide +kernel)

theorem space4126_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 83, 35, 7]) := by
  have h := frozenWangTable.lower_le_L0 190 space4126_orbit
  simpa only [lower190] using h

theorem space4127_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 80, 33, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 20), (128, 8), (80, 104), (33, 148), (4, 2), (2, 1)]
    (codeMat 417) (codeMat 98) (codeMat 140) false
    det417 det98 inv98
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space4127_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 80, 33, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space4127_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
