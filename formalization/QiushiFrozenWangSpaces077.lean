import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2464_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 32, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 166), (32, 9), (9, 2), (4, 8), (3, 32)]
    (codeMat 331) (codeMat 156) (codeMat 102) false
    det331 det156 inv156
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2464_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 32, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2464_orbit
  simpa only [lower103] using h

theorem space2465_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [81, 32, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(81, 132), (32, 3), (8, 2), (5, 8), (2, 32)]
    (codeMat 330) (codeMat 172) (codeMat 99) false
    det330 det172 inv172
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2465_lower : 15 ≤ frozenWangTable.L0 (spanCodes [81, 32, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2465_orbit
  simpa only [lower103] using h

theorem space2466_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [69, 32, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(69, 164), (32, 32), (17, 10), (9, 2), (3, 9)]
    (codeMat 339) (codeMat 282) (codeMat 267) false
    det339 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2466_lower : 15 ≤ frozenWangTable.L0 (spanCodes [69, 32, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2466_orbit
  simpa only [lower103] using h

theorem space2467_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [69, 33, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(69, 164), (33, 34), (17, 10), (9, 2), (3, 9)]
    (codeMat 275) (codeMat 314) (codeMat 271) false
    det275 det314 inv314
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2467_lower : 15 ≤ frozenWangTable.L0 (spanCodes [69, 33, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2467_orbit
  simpa only [lower103] using h

theorem space2468_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 48, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 133), (48, 1), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    det266 det394 inv394
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2468_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 48, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2468_orbit
  simpa only [lower103] using h

theorem space2469_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [80, 49, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(80, 175), (49, 11), (9, 2), (4, 32), (3, 40)]
    (codeMat 331) (codeMat 410) (codeMat 331) false
    det331 det410 inv410
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2469_lower : 15 ≤ frozenWangTable.L0 (spanCodes [80, 49, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2469_orbit
  simpa only [lower103] using h

theorem space2470_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [81, 48, 9, 5, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(81, 175), (48, 9), (9, 2), (5, 32), (3, 40)]
    (codeMat 267) (codeMat 442) (codeMat 334) false
    det267 det442 inv442
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2470_lower : 15 ≤ frozenWangTable.L0 (spanCodes [81, 48, 9, 5, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2470_orbit
  simpa only [lower103] using h

theorem space2471_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [68, 37, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(68, 164), (37, 34), (16, 1), (8, 2), (2, 9)]
    (codeMat 346) (codeMat 298) (codeMat 270) false
    det346 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2471_lower : 15 ≤ frozenWangTable.L0 (spanCodes [68, 37, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2471_orbit
  simpa only [lower103] using h

theorem space2472_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [81, 48, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(81, 133), (48, 3), (8, 2), (5, 32), (2, 40)]
    (codeMat 330) (codeMat 426) (codeMat 335) false
    det330 det426 inv426
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2472_lower : 15 ≤ frozenWangTable.L0 (spanCodes [81, 48, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2472_orbit
  simpa only [lower103] using h

theorem space2473_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [128, 84, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(128, 2), (84, 84), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    det161 det266 inv266
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2473_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 84, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2473_orbit
  simpa only [lower101] using h

theorem space2474_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [132, 84, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(132, 118), (84, 84), (8, 32), (2, 9), (1, 8)]
    (codeMat 177) (codeMat 282) (codeMat 267) true
    det177 det282 inv282
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2474_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 84, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2474_orbit
  simpa only [lower101] using h

theorem space2475_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [133, 65, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(133, 135), (65, 40), (21, 132), (8, 32), (2, 2)]
    (codeMat 143) (codeMat 298) (codeMat 270) true
    det143 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2475_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 65, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2475_orbit
  simpa only [lower103] using h

theorem space2476_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 69, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 32), (69, 166), (17, 10), (9, 9), (3, 2)]
    (codeMat 267) (codeMat 313) (codeMat 313) true
    det267 det313 inv313
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2476_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 69, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2476_orbit
  simpa only [lower103] using h

theorem space2477_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [129, 69, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(129, 34), (69, 164), (17, 10), (9, 9), (3, 2)]
    (codeMat 331) (codeMat 281) (codeMat 281) true
    det331 det281 inv281
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2477_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 69, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2477_orbit
  simpa only [lower103] using h

theorem space2478_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [133, 65, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(133, 175), (65, 40), (21, 166), (9, 32), (3, 2)]
    (codeMat 206) (codeMat 282) (codeMat 267) true
    det206 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2478_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 65, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2478_orbit
  simpa only [lower103] using h

theorem space2479_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [144, 84, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(144, 2), (84, 116), (8, 32), (2, 1), (1, 8)]
    (codeMat 177) (codeMat 266) (codeMat 266) true
    det177 det266 inv266
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2479_lower : 15 ≤ frozenWangTable.L0 (spanCodes [144, 84, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2479_orbit
  simpa only [lower101] using h

theorem space2480_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [132, 68, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(132, 132), (68, 164), (16, 1), (8, 9), (2, 2)]
    (codeMat 266) (codeMat 267) (codeMat 282) true
    det266 det267 inv267
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2480_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 68, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2480_orbit
  simpa only [lower103] using h

theorem space2481_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [129, 65, 21, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(129, 11), (65, 8), (21, 166), (9, 32), (3, 2)]
    (codeMat 205) (codeMat 282) (codeMat 267) true
    det205 det282 inv282
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2481_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 65, 21, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 103 space2481_orbit
  simpa only [lower103] using h

theorem space2482_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [128, 65, 21, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(128, 3), (65, 8), (21, 132), (8, 32), (2, 2)]
    (codeMat 141) (codeMat 298) (codeMat 270) true
    det141 det298 inv298
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2482_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 65, 21, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2482_orbit
  simpa only [lower103] using h

theorem space2483_orbit :
    frozenWangTable.OrbitImage 101 (spanCodes [148, 84, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 101 [(148, 118), (84, 116), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    det161 det282 inv282
    (by rw [basis101]; decide +kernel)
    (by rw [basis101]; decide +kernel)

theorem space2483_lower : 15 ≤ frozenWangTable.L0 (spanCodes [148, 84, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 101 space2483_orbit
  simpa only [lower101] using h

theorem space2484_orbit :
    frozenWangTable.OrbitImage 192 (spanCodes [146, 82, 50, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 192 [(146, 128), (82, 383), (50, 10), (10, 42), (6, 1)]
    (codeMat 465) (codeMat 117) (codeMat 380) false
    det465 det117 inv117
    (by rw [basis192]; decide +kernel)
    (by rw [basis192]; decide +kernel)

theorem space2484_lower : 15 ≤ frozenWangTable.L0 (spanCodes [146, 82, 50, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 192 space2484_orbit
  simpa only [lower192] using h

theorem space2485_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [128, 83, 32, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(128, 192), (83, 363), (32, 36), (10, 53), (7, 16)]
    (codeMat 267) (codeMat 339) (codeMat 467) false
    det267 det339 inv339
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space2485_lower : 15 ≤ frozenWangTable.L0 (spanCodes [128, 83, 32, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 220 space2485_orbit
  simpa only [lower220] using h

theorem space2486_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [129, 69, 37, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(129, 136), (69, 224), (37, 28), (17, 10), (9, 3), (3, 8)]
    (codeMat 331) (codeMat 281) (codeMat 281) false
    det331 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2486_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 69, 37, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2486_orbit
  simpa only [lower35] using h

theorem space2487_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [132, 69, 32, 17, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(132, 224), (69, 255), (32, 128), (17, 11), (9, 9), (3, 3)]
    (codeMat 275) (codeMat 281) (codeMat 281) true
    det275 det281 inv281
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2487_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 69, 32, 17, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2487_orbit
  simpa only [lower35] using h

theorem space2488_orbit :
    frozenWangTable.OrbitImage 197 (spanCodes [161, 66, 18, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 197 [(161, 142), (66, 356), (18, 1), (10, 324), (4, 448)]
    (codeMat 115) (codeMat 358) (codeMat 158) false
    det115 det358 inv358
    (by rw [basis197]; decide +kernel)
    (by rw [basis197]; decide +kernel)

theorem space2488_lower : 15 ≤ frozenWangTable.L0 (spanCodes [161, 66, 18, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 197 space2488_orbit
  simpa only [lower197] using h

theorem space2489_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [129, 68, 36, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(129, 28), (68, 224), (36, 128), (16, 1), (8, 8), (2, 3)]
    (codeMat 282) (codeMat 266) (codeMat 266) true
    det282 det266 inv266
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2489_lower : 15 ≤ frozenWangTable.L0 (spanCodes [129, 68, 36, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2489_orbit
  simpa only [lower35] using h

theorem space2490_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [132, 68, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(132, 96), (68, 224), (33, 28), (16, 1), (8, 3), (2, 8)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    det266 det267 inv267
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2490_lower : 15 ≤ frozenWangTable.L0 (spanCodes [132, 68, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2490_orbit
  simpa only [lower35] using h

theorem space2491_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 80, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 150), (80, 232), (34, 22), (10, 30), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 185) (codeMat 481) false
    det401 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2491_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 80, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2491_orbit
  simpa only [lower35] using h

theorem space2492_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 80, 32, 9, 4, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 22), (80, 252), (32, 3), (9, 9), (4, 2), (3, 130)]
    (codeMat 267) (codeMat 157) (codeMat 486) true
    det267 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2492_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 80, 32, 9, 4, 3]) := by
  have h := frozenWangTable.lower_le_L0 35 space2492_orbit
  simpa only [lower35] using h

theorem space2493_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 80, 32, 8, 4, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 20), (80, 96), (32, 1), (8, 8), (4, 2), (2, 128)]
    (codeMat 266) (codeMat 140) (codeMat 98) true
    det266 det140 inv140
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2493_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 80, 32, 8, 4, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2493_orbit
  simpa only [lower35] using h

theorem space2494_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 80, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 128), (80, 224), (34, 20), (10, 28), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 169) (codeMat 225) false
    det273 det169 inv169
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2494_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 80, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2494_orbit
  simpa only [lower35] using h

theorem space2495_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [272, 80, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(272, 96), (80, 224), (32, 8), (10, 28), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    det273 det141 inv141
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2495_lower : 15 ≤ frozenWangTable.L0 (spanCodes [272, 80, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2495_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
