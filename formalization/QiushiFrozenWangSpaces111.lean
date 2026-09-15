import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3552_orbit :
    frozenWangTable.OrbitImage 274 (spanCodes [275, 144, 66, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 274 [(275, 241), (144, 1), (66, 80), (10, 82)]
    (codeMat 102) (codeMat 302) (codeMat 302) false
    det102 det302 inv302
    (by rw [basis274]; decide +kernel)
    (by rw [basis274]; decide +kernel)

theorem space3552_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 66, 10]) := by
  have h := frozenWangTable.lower_le_L0 274 space3552_orbit
  simpa only [lower274] using h

theorem space3553_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 147, 65, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 395), (147, 11), (65, 32), (10, 42)]
    (codeMat 334) (codeMat 318) (codeMat 299) true
    det334 det318 inv318
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3553_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 65, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3553_orbit
  simpa only [lower298] using h

theorem space3554_orbit :
    frozenWangTable.OrbitImage 267 (spanCodes [257, 192, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 267 [(257, 118), (192, 1), (18, 32), (10, 34)]
    (codeMat 212) (codeMat 281) (codeMat 281) true
    det212 det281 inv281
    (by rw [basis267]; decide +kernel)
    (by rw [basis267]; decide +kernel)

theorem space3554_lower : 16 ≤ frozenWangTable.L0 (spanCodes [257, 192, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 267 space3554_orbit
  simpa only [lower267] using h

theorem space3555_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 144, 67, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 395), (144, 32), (67, 43), (10, 42)]
    (codeMat 407) (codeMat 309) (codeMat 309) true
    det407 det309 inv309
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3555_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 67, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3555_orbit
  simpa only [lower298] using h

theorem space3556_orbit :
    frozenWangTable.OrbitImage 298 (spanCodes [275, 146, 65, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 298 [(275, 417), (146, 1), (65, 32), (10, 42)]
    (codeMat 335) (codeMat 302) (codeMat 302) true
    det335 det302 inv302
    (by rw [basis298]; decide +kernel)
    (by rw [basis298]; decide +kernel)

theorem space3556_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 146, 65, 10]) := by
  have h := frozenWangTable.lower_le_L0 298 space3556_orbit
  simpa only [lower298] using h

theorem space3557_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 149, 65, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 369), (149, 368), (65, 2), (10, 274)]
    (codeMat 117) (codeMat 444) (codeMat 110) false
    det117 det444 inv444
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3557_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 149, 65, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3557_orbit
  simpa only [lower276] using h

theorem space3558_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [275, 165, 113, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(275, 98), (165, 99), (113, 257), (10, 371)]
    (codeMat 375) (codeMat 501) (codeMat 494) false
    det375 det501 inv501
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space3558_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 165, 113, 10]) := by
  have h := frozenWangTable.lower_le_L0 336 space3558_orbit
  simpa only [lower336] using h

theorem space3559_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [260, 195, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(260, 3), (195, 2), (23, 96), (10, 304)]
    (codeMat 85) (codeMat 236) (codeMat 123) false
    det85 det236 inv236
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3559_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 195, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3559_orbit
  simpa only [lower278] using h

theorem space3560_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 210, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 115), (210, 338), (10, 322), (6, 1)]
    (codeMat 241) (codeMat 499) (codeMat 382) false
    det241 det499 inv499
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3560_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 210, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 338 space3560_orbit
  simpa only [lower338] using h

theorem space3561_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 211, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 99), (211, 96), (10, 304), (7, 2)]
    (codeMat 141) (codeMat 348) (codeMat 125) true
    det141 det348 inv348
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3561_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 211, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 278 space3561_orbit
  simpa only [lower278] using h

theorem space3562_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 144, 113, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 99), (144, 2), (113, 368), (10, 274)]
    (codeMat 174) (codeMat 380) (codeMat 117) false
    det174 det380 inv380
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3562_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 144, 113, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3562_orbit
  simpa only [lower276] using h

theorem space3563_orbit :
    frozenWangTable.OrbitImage 336 (spanCodes [275, 149, 116, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 336 [(275, 273), (149, 17), (116, 114), (10, 371)]
    (codeMat 382) (codeMat 375) (codeMat 491) false
    det382 det375 inv375
    (by rw [basis336]; decide +kernel)
    (by rw [basis336]; decide +kernel)

theorem space3563_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 149, 116, 10]) := by
  have h := frozenWangTable.lower_le_L0 336 space3563_orbit
  simpa only [lower336] using h

theorem space3564_orbit :
    frozenWangTable.OrbitImage 338 (spanCodes [275, 195, 34, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 338 [(275, 305), (195, 16), (34, 323), (10, 322)]
    (codeMat 234) (codeMat 491) (codeMat 375) false
    det234 det491 inv491
    (by rw [basis338]; decide +kernel)
    (by rw [basis338]; decide +kernel)

theorem space3564_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 195, 34, 10]) := by
  have h := frozenWangTable.lower_le_L0 338 space3564_orbit
  simpa only [lower338] using h

theorem space3565_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 210, 51, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (210, 306), (51, 336), (10, 304)]
    (codeMat 142) (codeMat 244) (codeMat 95) false
    det142 det244 inv244
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3565_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 210, 51, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3565_orbit
  simpa only [lower278] using h

theorem space3566_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 211, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (211, 336), (50, 306), (10, 304)]
    (codeMat 86) (codeMat 412) (codeMat 111) true
    det86 det412 inv412
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3566_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 211, 50, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3566_orbit
  simpa only [lower278] using h

theorem space3567_orbit :
    frozenWangTable.OrbitImage 276 (spanCodes [275, 212, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 276 [(275, 369), (212, 370), (53, 272), (10, 274)]
    (codeMat 94) (codeMat 415) (codeMat 253) true
    det94 det415 inv415
    (by rw [basis276]; decide +kernel)
    (by rw [basis276]; decide +kernel)

theorem space3567_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 212, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 276 space3567_orbit
  simpa only [lower276] using h

theorem space3568_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 129, 83, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 94), (129, 332), (83, 69), (48, 16), (10, 264)]
    (codeMat 214) (codeMat 481) (codeMat 185) false
    det214 det481 inv481
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3568_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 129, 83, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3568_orbit
  simpa only [lower150] using h

theorem space3569_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 145, 66, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 342), (145, 68), (66, 265), (48, 16), (10, 264)]
    (codeMat 86) (codeMat 417) (codeMat 177) false
    det86 det417 inv417
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3569_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 145, 66, 48, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3569_orbit
  simpa only [lower150] using h

theorem space3570_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 147, 67, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 94), (147, 69), (67, 265), (53, 280), (10, 264)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    det95 det419 inv419
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3570_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 147, 67, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3570_orbit
  simpa only [lower150] using h

theorem space3571_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 209, 51, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 275), (209, 349), (51, 259), (10, 326), (7, 1)]
    (codeMat 177) (codeMat 241) (codeMat 489) false
    det177 det241 inv241
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3571_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 209, 51, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 150 space3571_orbit
  simpa only [lower150] using h

theorem space3572_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 209, 55, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 307), (209, 97), (55, 304), (10, 96)]
    (codeMat 95) (codeMat 230) (codeMat 159) false
    det95 det230 inv230
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3572_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 209, 55, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3572_orbit
  simpa only [lower278] using h

theorem space3573_orbit :
    frozenWangTable.OrbitImage 278 (spanCodes [275, 211, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 278 [(275, 339), (211, 336), (53, 97), (10, 96)]
    (codeMat 123) (codeMat 244) (codeMat 95) true
    det123 det244 inv244
    (by rw [basis278]; decide +kernel)
    (by rw [basis278]; decide +kernel)

theorem space3573_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 211, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 278 space3573_orbit
  simpa only [lower278] using h

theorem space3574_orbit :
    frozenWangTable.OrbitImage 152 (spanCodes [275, 162, 66, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 152 [(275, 174), (162, 164), (66, 97), (10, 96), (6, 16)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    det142 det417 inv417
    (by rw [basis152]; decide +kernel)
    (by rw [basis152]; decide +kernel)

theorem space3574_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 162, 66, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 152 space3574_orbit
  simpa only [lower152] using h

theorem space3575_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [275, 146, 83, 53, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(275, 342), (146, 1), (83, 333), (53, 280), (10, 264)]
    (codeMat 159) (codeMat 355) (codeMat 190) false
    det159 det355 inv355
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3575_lower : 16 ≤ frozenWangTable.L0 (spanCodes [275, 146, 83, 53, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3575_orbit
  simpa only [lower150] using h

theorem space3576_orbit :
    frozenWangTable.OrbitImage 150 (spanCodes [260, 198, 37, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 150 [(260, 16), (198, 280), (37, 258), (23, 69), (10, 326)]
    (codeMat 106) (codeMat 234) (codeMat 461) false
    det106 det234 inv234
    (by rw [basis150]; decide +kernel)
    (by rw [basis150]; decide +kernel)

theorem space3576_lower : 16 ≤ frozenWangTable.L0 (spanCodes [260, 198, 37, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 150 space3576_orbit
  simpa only [lower150] using h

theorem space3577_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 16, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 132), (16, 8), (8, 32), (4, 2), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    det273 det98 inv98
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3577_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 16, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3577_orbit
  simpa only [lower103] using h

theorem space3578_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 17, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 133), (17, 33), (9, 40), (4, 2), (3, 1)]
    (codeMat 281) (codeMat 225) (codeMat 169) false
    det281 det225 inv225
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3578_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 17, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3578_orbit
  simpa only [lower103] using h

theorem space3579_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [273, 32, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(273, 84), (32, 1), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    det266 det140 inv140
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3579_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 32, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 101 space3579_orbit
  simpa only [lower101] using h

theorem space3580_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 33, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 166), (33, 10), (9, 3), (5, 8), (3, 40)]
    (codeMat 331) (codeMat 185) (codeMat 481) false
    det331 det185 inv185
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3580_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 33, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3580_orbit
  simpa only [lower103] using h

theorem space3581_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [272, 32, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(272, 118), (32, 9), (9, 2), (4, 8), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    det267 det156 inv156
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3581_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 32, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 101 space3581_orbit
  simpa only [lower101] using h

theorem space3582_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [273, 32, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(273, 140), (32, 2), (8, 3), (5, 8), (2, 32)]
    (codeMat 330) (codeMat 169) (codeMat 225) false
    det330 det169 inv169
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3582_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 32, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3582_orbit
  simpa only [lower103] using h

theorem space3583_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 36, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 164), (36, 2), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 161) (codeMat 161) false
    det267 det161 inv161
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3583_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 36, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 103 space3583_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
