import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0928_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 130, 66, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 284), (130, 438), (66, 406), (35, 287), (19, 306), (10, 404)]
    (codeMat 486) (codeMat 188) (codeMat 103) false
    det486 det188 inv188
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0928_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 66, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0928_orbit
  simpa only [lower55] using h

theorem space0929_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 128, 65, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 3), (128, 438), (65, 2), (37, 139), (19, 166), (10, 306)]
    (codeMat 501) (codeMat 188) (codeMat 103) false
    det501 det188 inv188
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0929_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 128, 65, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0929_orbit
  simpa only [lower55] using h

theorem space0930_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 130, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 284), (130, 32), (66, 406), (38, 287), (19, 166), (10, 404)]
    (codeMat 494) (codeMat 172) (codeMat 99) false
    det494 det172 inv172
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0930_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 130, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0930_orbit
  simpa only [lower55] using h

theorem space0931_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 408), (128, 32), (66, 304), (32, 45), (19, 404), (10, 306)]
    (codeMat 358) (codeMat 396) (codeMat 106) false
    det358 det396 inv396
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0931_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0931_orbit
  simpa only [lower55] using h

theorem space0932_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 130, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 170), (130, 438), (66, 406), (32, 45), (19, 306), (10, 404)]
    (codeMat 486) (codeMat 412) (codeMat 111) false
    det486 det412 inv412
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0932_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 130, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0932_orbit
  simpa only [lower55] using h

theorem space0933_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 130, 67, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 440), (130, 32), (67, 272), (37, 441), (19, 404), (10, 166)]
    (codeMat 302) (codeMat 204) (codeMat 114) false
    det302 det204 inv204
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0933_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 130, 67, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0933_orbit
  simpa only [lower55] using h

theorem space0934_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 130, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 437), (130, 438), (66, 436), (32, 45), (19, 166), (10, 404)]
    (codeMat 500) (codeMat 468) (codeMat 87) false
    det500 det468 inv468
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0934_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0934_orbit
  simpa only [lower55] using h

theorem space0935_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 67, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 133), (131, 134), (67, 132), (33, 441), (19, 166), (10, 306)]
    (codeMat 372) (codeMat 492) (codeMat 115) false
    det372 det492 inv492
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0935_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0935_orbit
  simpa only [lower55] using h

theorem space0936_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 130, 66, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 3), (130, 2), (66, 436), (38, 139), (19, 306), (10, 404)]
    (codeMat 501) (codeMat 116) (codeMat 92) false
    det501 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0936_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 130, 66, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0936_orbit
  simpa only [lower55] using h

theorem space0937_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 131, 65, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 136), (131, 304), (65, 32), (38, 139), (19, 306), (10, 404)]
    (codeMat 302) (codeMat 116) (codeMat 92) false
    det302 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0937_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 131, 65, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0937_orbit
  simpa only [lower55] using h

theorem space0938_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 128, 65, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 316), (128, 438), (65, 32), (38, 441), (19, 306), (10, 166)]
    (codeMat 494) (codeMat 500) (codeMat 94) false
    det494 det500 inv500
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0938_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 128, 65, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0938_orbit
  simpa only [lower55] using h

theorem space0939_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [261, 131, 64, 36, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(261, 437), (131, 436), (64, 438), (36, 45), (19, 404), (10, 166)]
    (codeMat 501) (codeMat 460) (codeMat 122) false
    det501 det460 inv460
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0939_lower : 14 ≤ frozenWangTable.L0 (spanCodes [261, 131, 64, 36, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0939_orbit
  simpa only [lower55] using h

theorem space0940_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 130, 66, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (130, 438), (66, 436), (35, 139), (19, 166), (10, 404)]
    (codeMat 500) (codeMat 244) (codeMat 95) false
    det500 det244 inv244
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0940_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 130, 66, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0940_orbit
  simpa only [lower55] using h

theorem space0941_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 128, 65, 35, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 439), (128, 2), (65, 438), (35, 287), (19, 306), (10, 166)]
    (codeMat 500) (codeMat 380) (codeMat 117) false
    det500 det380 inv380
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0941_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0941_orbit
  simpa only [lower55] using h

theorem space0942_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 130, 66, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 439), (130, 438), (66, 436), (33, 287), (19, 166), (10, 404)]
    (codeMat 500) (codeMat 500) (codeMat 94) false
    det500 det500 inv500
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0942_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0942_orbit
  simpa only [lower55] using h

theorem space0943_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 128, 66, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (128, 2), (66, 134), (33, 287), (19, 404), (10, 166)]
    (codeMat 372) (codeMat 116) (codeMat 92) false
    det372 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0943_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 128, 66, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0943_orbit
  simpa only [lower55] using h

theorem space0944_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 131, 64, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 284), (131, 406), (64, 32), (33, 287), (19, 404), (10, 166)]
    (codeMat 486) (codeMat 116) (codeMat 92) false
    det486 det116 inv116
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0944_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 131, 64, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0944_orbit
  simpa only [lower55] using h

theorem space0945_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 67, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 135), (131, 134), (67, 132), (32, 45), (19, 166), (10, 306)]
    (codeMat 372) (codeMat 460) (codeMat 122) false
    det372 det460 inv460
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0945_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 67, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0945_orbit
  simpa only [lower55] using h

theorem space0946_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 131, 65, 37, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 1), (131, 134), (65, 2), (37, 139), (19, 166), (10, 404)]
    (codeMat 309) (codeMat 140) (codeMat 98) false
    det309 det140 inv140
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0946_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 131, 65, 37, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0946_orbit
  simpa only [lower55] using h

theorem space0947_orbit :
    frozenWangTable.OrbitImage 51 (spanCodes [258, 128, 64, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 51 [(258, 197), (128, 3), (64, 2), (38, 232), (19, 152), (10, 80)]
    (codeMat 92) (codeMat 286) (codeMat 303) false
    det92 det286 inv286
    (by rw [basis51]; decide +kernel)
    (by rw [basis51]; decide +kernel)

theorem space0947_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 51 space0947_orbit
  simpa only [lower51] using h

theorem space0948_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 131, 67, 38, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 440), (131, 272), (67, 304), (38, 441), (19, 166), (10, 306)]
    (codeMat 359) (codeMat 156) (codeMat 102) false
    det359 det156 inv156
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0948_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 67, 38, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0948_orbit
  simpa only [lower55] using h

theorem space0949_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [263, 129, 66, 32, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(263, 135), (129, 134), (66, 132), (32, 45), (19, 166), (10, 306)]
    (codeMat 317) (codeMat 460) (codeMat 122) false
    det317 det460 inv460
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0949_lower : 14 ≤ frozenWangTable.L0 (spanCodes [263, 129, 66, 32, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0949_orbit
  simpa only [lower55] using h

theorem space0950_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [262, 128, 67, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(262, 439), (128, 438), (67, 436), (33, 287), (19, 166), (10, 404)]
    (codeMat 445) (codeMat 500) (codeMat 94) false
    det445 det500 inv500
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0950_lower : 14 ≤ frozenWangTable.L0 (spanCodes [262, 128, 67, 33, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0950_orbit
  simpa only [lower55] using h

theorem space0951_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [260, 130, 64, 34, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(260, 3), (130, 2), (64, 438), (34, 139), (19, 306), (10, 166)]
    (codeMat 445) (codeMat 124) (codeMat 124) false
    det445 det124 inv124
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0951_lower : 14 ≤ frozenWangTable.L0 (spanCodes [260, 130, 64, 34, 19, 10]) := by
  have h := frozenWangTable.lower_le_L0 55 space0951_orbit
  simpa only [lower55] using h

theorem space0952_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 130, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 450), (130, 390), (64, 1), (33, 208), (19, 112), (10, 456), (4, 128)]
    (codeMat 92) (codeMat 177) (codeMat 417) false
    det92 det177 inv177
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0952_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 130, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0952_orbit
  simpa only [lower17] using h

theorem space0953_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 131, 64, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 450), (131, 391), (64, 1), (33, 80), (19, 440), (10, 456), (4, 128)]
    (codeMat 84) (codeMat 179) (codeMat 421) false
    det84 det179 inv179
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0953_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 131, 64, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0953_orbit
  simpa only [lower17] using h

theorem space0954_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [384, 65, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(384, 3), (65, 45), (33, 274), (19, 166), (10, 404), (4, 438)]
    (codeMat 159) (codeMat 445) (codeMat 478) true
    det159 det445 inv445
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0954_lower : 14 ≤ frozenWangTable.L0 (spanCodes [384, 65, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0954_orbit
  simpa only [lower55] using h

theorem space0955_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 402), (128, 63), (66, 457), (33, 80), (19, 440), (10, 456), (4, 128)]
    (codeMat 86) (codeMat 179) (codeMat 421) false
    det86 det179 inv179
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0955_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0955_orbit
  simpa only [lower17] using h

theorem space0956_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [258, 129, 66, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(258, 274), (129, 502), (66, 457), (33, 208), (19, 112), (10, 456), (4, 128)]
    (codeMat 94) (codeMat 177) (codeMat 417) false
    det94 det177 inv177
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0956_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 129, 66, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0956_orbit
  simpa only [lower17] using h

theorem space0957_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 129, 64, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 402), (129, 457), (64, 63), (34, 208), (19, 456), (10, 440), (4, 128)]
    (codeMat 95) (codeMat 107) (codeMat 428) false
    det95 det107 inv107
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0957_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 129, 64, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0957_orbit
  simpa only [lower17] using h

theorem space0958_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [259, 128, 65, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(259, 450), (128, 1), (65, 390), (34, 80), (19, 456), (10, 112), (4, 128)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    det84 det106 inv106
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0958_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 65, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0958_orbit
  simpa only [lower17] using h

theorem space0959_orbit :
    frozenWangTable.OrbitImage 17 (spanCodes [257, 129, 66, 34, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 17 [(257, 274), (129, 457), (66, 502), (34, 80), (19, 456), (10, 112), (4, 128)]
    (codeMat 87) (codeMat 106) (codeMat 396) false
    det87 det106 inv106
    (by rw [basis17]; decide +kernel)
    (by rw [basis17]; decide +kernel)

theorem space0959_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 66, 34, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 17 space0959_orbit
  simpa only [lower17] using h


end QiushiMatmul.FrozenWang
