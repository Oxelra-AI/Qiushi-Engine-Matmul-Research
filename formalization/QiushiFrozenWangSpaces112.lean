import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3584_orbit :
    frozenWangTable.OrbitImage 157 (spanCodes [256, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 157 [(256, 128), (35, 42), (19, 43), (10, 30), (5, 32)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    det266 det122 inv122
    (by rw [basis157]; decide +kernel)
    (by rw [basis157]; decide +kernel)

theorem space3584_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 157 space3584_orbit
  simpa only [lower157] using h

theorem space3585_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 32, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 173), (32, 2), (18, 32), (10, 35), (7, 9)]
    (codeMat 346) (codeMat 233) (codeMat 233) false
    det346 det233 inv233
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3585_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 32, 18, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 103 space3585_orbit
  simpa only [lower103] using h

theorem space3586_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 34, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 164), (34, 11), (18, 3), (10, 43), (6, 9)]
    (codeMat 339) (codeMat 122) (codeMat 460) false
    det339 det122 inv122
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3586_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 34, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 103 space3586_orbit
  simpa only [lower103] using h

theorem space3587_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [257, 32, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(257, 118), (32, 8), (18, 2), (10, 34), (4, 9)]
    (codeMat 275) (codeMat 92) (codeMat 116) false
    det275 det92 inv92
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3587_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 32, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 101 space3587_orbit
  simpa only [lower101] using h

theorem space3588_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [273, 48, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(273, 140), (48, 8), (8, 32), (4, 2), (2, 3)]
    (codeMat 401) (codeMat 114) (codeMat 204) false
    det401 det114 inv114
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3588_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 48, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3588_orbit
  simpa only [lower103] using h

theorem space3589_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 164), (49, 33), (9, 40), (4, 2), (3, 3)]
    (codeMat 409) (codeMat 241) (codeMat 489) false
    det409 det241 inv241
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3589_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3589_orbit
  simpa only [lower103] using h

theorem space3590_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 64, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 132), (64, 2), (16, 8), (8, 1), (2, 32)]
    (codeMat 98) (codeMat 273) (codeMat 273) true
    det98 det273 inv273
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3590_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 64, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3590_orbit
  simpa only [lower103] using h

theorem space3591_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [275, 83, 51, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(275, 461), (83, 493), (51, 463), (10, 118), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    det305 det141 inv141
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3591_lower : 15 ≤ frozenWangTable.L0 (spanCodes [275, 83, 51, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 144 space3591_orbit
  simpa only [lower144] using h

theorem space3592_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 64, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 118), (64, 128), (32, 8), (10, 22), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 156) (codeMat 102) false
    det273 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3592_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 64, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3592_orbit
  simpa only [lower35] using h

theorem space3593_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 66, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 252), (66, 148), (34, 28), (10, 20), (4, 3), (1, 2)]
    (codeMat 401) (codeMat 172) (codeMat 99) false
    det401 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3593_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 66, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3593_orbit
  simpa only [lower35] using h

theorem space3594_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 64, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 246), (64, 128), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 188) (codeMat 103) false
    det273 det188 inv188
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3594_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 64, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3594_orbit
  simpa only [lower35] using h

theorem space3595_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 66, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 126), (66, 150), (32, 8), (10, 22), (4, 1), (1, 2)]
    (codeMat 401) (codeMat 156) (codeMat 102) false
    det401 det156 inv156
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3595_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 66, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3595_orbit
  simpa only [lower35] using h

theorem space3596_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 68, 32, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 96), (68, 20), (32, 8), (8, 1), (2, 128), (1, 2)]
    (codeMat 266) (codeMat 161) (codeMat 161) true
    det266 det161 inv161
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3596_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 68, 32, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3596_orbit
  simpa only [lower35] using h

theorem space3597_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 67, 36, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (67, 495), (36, 1), (23, 118), (10, 463)]
    (codeMat 491) (codeMat 158) (codeMat 358) true
    det491 det158 inv158
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3597_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 67, 36, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3597_orbit
  simpa only [lower144] using h

theorem space3598_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 66, 32, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (66, 495), (32, 1), (23, 441), (10, 463)]
    (codeMat 426) (codeMat 142) (codeMat 354) true
    det426 det142 inv142
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3598_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 66, 32, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3598_orbit
  simpa only [lower144] using h

theorem space3599_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 80, 32, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 116), (80, 96), (32, 9), (8, 8), (5, 2), (2, 128)]
    (codeMat 266) (codeMat 172) (codeMat 99) true
    det266 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3599_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 80, 32, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space3599_orbit
  simpa only [lower35] using h

theorem space3600_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [274, 82, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(274, 118), (82, 246), (32, 8), (10, 30), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 157) (codeMat 486) false
    det273 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3600_lower : 15 ≤ frozenWangTable.L0 (spanCodes [274, 82, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space3600_orbit
  simpa only [lower35] using h

theorem space3601_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 128, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 164), (128, 2), (17, 33), (9, 9), (3, 32)]
    (codeMat 99) (codeMat 267) (codeMat 282) true
    det99 det267 inv267
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3601_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3601_orbit
  simpa only [lower103] using h

theorem space3602_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 132, 32, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (132, 34), (32, 1), (23, 441), (10, 118)]
    (codeMat 298) (codeMat 86) (codeMat 212) true
    det298 det86 inv86
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3602_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 132, 32, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3602_orbit
  simpa only [lower144] using h

theorem space3603_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 96), (128, 128), (32, 1), (16, 2), (10, 22), (4, 8)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    det266 det92 inv92
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3603_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3603_orbit
  simpa only [lower35] using h

theorem space3604_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 32, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 232), (130, 128), (32, 3), (16, 2), (10, 20), (6, 8)]
    (codeMat 330) (codeMat 116) (codeMat 92) false
    det330 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3604_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 32, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3604_orbit
  simpa only [lower35] using h

theorem space3605_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 129, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 96), (129, 232), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    det330 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3605_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 129, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3605_orbit
  simpa only [lower35] using h

theorem space3606_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 131, 34, 18, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 252), (131, 224), (34, 10), (18, 8), (10, 136), (6, 3)]
    (codeMat 275) (codeMat 124) (codeMat 124) true
    det275 det124 inv124
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3606_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 131, 34, 18, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3606_orbit
  simpa only [lower35] using h

theorem space3607_orbit :
    frozenWangTable.OrbitImage 144 (spanCodes [260, 133, 36, 23, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 144 [(260, 2), (133, 495), (36, 1), (23, 463), (10, 440)]
    (codeMat 491) (codeMat 84) (codeMat 84) true
    det491 det84 inv84
    (by rw [basis144]; decide +kernel)
    (by rw [basis144]; decide +kernel)

theorem space3607_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 133, 36, 23, 10]) := by
  have h := frozenWangTable.lower_le_L0 144 space3607_orbit
  simpa only [lower144] using h

theorem space3608_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 128, 32, 16, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 224), (128, 128), (32, 3), (16, 2), (10, 22), (6, 8)]
    (codeMat 266) (codeMat 124) (codeMat 124) false
    det266 det124 inv124
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3608_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 128, 32, 16, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 35 space3608_orbit
  simpa only [lower35] using h

theorem space3609_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 130, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (130, 128), (32, 1), (16, 2), (10, 22), (4, 8)]
    (codeMat 330) (codeMat 92) (codeMat 116) false
    det330 det92 inv92
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3609_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 130, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3609_orbit
  simpa only [lower35] using h

theorem space3610_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [259, 131, 32, 16, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(259, 104), (131, 232), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 266) (codeMat 94) (codeMat 500) false
    det266 det94 inv94
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3610_lower : 15 ≤ frozenWangTable.L0 (spanCodes [259, 131, 32, 16, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space3610_orbit
  simpa only [lower35] using h

theorem space3611_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [273, 129, 48, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(273, 116), (129, 96), (48, 2), (8, 128), (4, 9), (2, 8)]
    (codeMat 273) (codeMat 116) (codeMat 92) true
    det273 det116 inv116
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space3611_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 129, 48, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space3611_orbit
  simpa only [lower35] using h

theorem space3612_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [273, 128, 64, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(273, 84), (128, 8), (64, 1), (8, 2), (2, 32)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    det84 det273 inv273
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3612_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 128, 64, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 101 space3612_orbit
  simpa only [lower101] using h

theorem space3613_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [272, 129, 65, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(272, 175), (129, 10), (65, 8), (9, 32), (3, 3)]
    (codeMat 229) (codeMat 314) (codeMat 271) true
    det229 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3613_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 129, 65, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space3613_orbit
  simpa only [lower103] using h

theorem space3614_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [272, 128, 64, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(272, 118), (128, 9), (64, 1), (9, 2), (3, 32)]
    (codeMat 92) (codeMat 275) (codeMat 275) true
    det92 det275 inv275
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space3614_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 128, 64, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 101 space3614_orbit
  simpa only [lower101] using h

theorem space3615_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [273, 128, 65, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(273, 140), (128, 2), (65, 8), (8, 32), (2, 3)]
    (codeMat 165) (codeMat 298) (codeMat 270) true
    det165 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space3615_lower : 15 ≤ frozenWangTable.L0 (spanCodes [273, 128, 65, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space3615_orbit
  simpa only [lower103] using h


end QiushiMatmul.FrozenWang
