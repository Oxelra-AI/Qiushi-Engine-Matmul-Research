import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space0864_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 33), (64, 45), (32, 2), (19, 404), (10, 306), (5, 32)]
    (codeMat 85) (codeMat 157) (codeMat 486) true
    det85 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0864_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0864_orbit
  simpa only [lower55] using h

theorem space0865_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 65, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (65, 45), (32, 2), (19, 404), (10, 306), (5, 32)]
    (codeMat 84) (codeMat 157) (codeMat 486) true
    det84 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0865_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 65, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0865_orbit
  simpa only [lower55] using h

theorem space0866_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 437), (64, 45), (32, 2), (19, 306), (10, 404), (7, 438)]
    (codeMat 215) (codeMat 143) (codeMat 482) true
    det215 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0866_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0866_orbit
  simpa only [lower55] using h

theorem space0867_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 65, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (65, 45), (33, 34), (19, 166), (10, 306), (5, 32)]
    (codeMat 92) (codeMat 143) (codeMat 482) true
    det92 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0867_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 65, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0867_orbit
  simpa only [lower55] using h

theorem space0868_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 64, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 33), (64, 45), (33, 34), (19, 166), (10, 306), (5, 32)]
    (codeMat 93) (codeMat 143) (codeMat 482) true
    det93 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0868_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 64, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0868_orbit
  simpa only [lower55] using h

theorem space0869_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 64, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 408), (64, 45), (32, 32), (19, 166), (10, 404), (7, 438)]
    (codeMat 158) (codeMat 185) (codeMat 481) true
    det158 det185 inv185
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0869_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0869_orbit
  simpa only [lower55] using h

theorem space0870_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 65, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (65, 45), (34, 436), (19, 166), (10, 404), (6, 438)]
    (codeMat 159) (codeMat 157) (codeMat 486) true
    det159 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0870_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 65, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0870_orbit
  simpa only [lower55] using h

theorem space0871_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 66, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (66, 441), (34, 436), (19, 166), (10, 404), (6, 438)]
    (codeMat 156) (codeMat 157) (codeMat 486) true
    det156 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0871_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 66, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0871_orbit
  simpa only [lower55] using h

theorem space0872_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 437), (64, 45), (34, 436), (19, 166), (10, 404), (6, 438)]
    (codeMat 158) (codeMat 157) (codeMat 486) true
    det158 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0872_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0872_orbit
  simpa only [lower55] using h

theorem space0873_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (65, 45), (32, 2), (19, 306), (10, 404), (7, 438)]
    (codeMat 214) (codeMat 143) (codeMat 482) true
    det214 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0873_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0873_orbit
  simpa only [lower55] using h

theorem space0874_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 67, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (67, 287), (32, 2), (19, 404), (10, 306), (5, 32)]
    (codeMat 86) (codeMat 157) (codeMat 486) true
    det86 det157 inv157
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0874_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 67, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0874_orbit
  simpa only [lower55] using h

theorem space0875_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 66, 33, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 3), (66, 287), (33, 34), (19, 166), (10, 306), (5, 32)]
    (codeMat 95) (codeMat 143) (codeMat 482) true
    det95 det143 inv143
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0875_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 66, 33, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0875_orbit
  simpa only [lower55] using h

theorem space0876_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 65, 32, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 46), (65, 45), (32, 32), (19, 166), (10, 404), (7, 438)]
    (codeMat 159) (codeMat 185) (codeMat 481) true
    det159 det185 inv185
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0876_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 65, 32, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0876_orbit
  simpa only [lower55] using h

theorem space0877_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 64, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 408), (64, 45), (34, 406), (19, 306), (10, 404), (6, 438)]
    (codeMat 215) (codeMat 171) (codeMat 485) true
    det215 det171 inv171
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0877_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 64, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0877_orbit
  simpa only [lower55] using h

theorem space0878_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 64, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 170), (64, 45), (32, 32), (19, 404), (10, 166), (5, 2)]
    (codeMat 142) (codeMat 171) (codeMat 485) true
    det142 det171 inv171
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0878_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0878_orbit
  simpa only [lower55] using h

theorem space0879_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 128, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 135), (128, 45), (33, 132), (19, 166), (10, 404), (4, 2)]
    (codeMat 207) (codeMat 87) (codeMat 468) true
    det207 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0879_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 128, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0879_orbit
  simpa only [lower55] using h

theorem space0880_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 128, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 135), (128, 45), (35, 134), (19, 166), (10, 306), (4, 2)]
    (codeMat 142) (codeMat 94) (codeMat 500) true
    det142 det94 inv94
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0880_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 128, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0880_orbit
  simpa only [lower55] using h

theorem space0881_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 129, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (129, 441), (32, 2), (19, 404), (10, 166), (5, 438)]
    (codeMat 212) (codeMat 94) (codeMat 500) true
    det212 det94 inv94
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0881_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 129, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0881_orbit
  simpa only [lower55] using h

theorem space0882_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [320, 193, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(320, 3), (193, 139), (32, 438), (19, 404), (10, 306), (5, 2)]
    (codeMat 205) (codeMat 494) (codeMat 501) true
    det205 det494 inv494
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0882_lower : 14 ≤ frozenWangTable.L0 (spanCodes [320, 193, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0882_orbit
  simpa only [lower55] using h

theorem space0883_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 128, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 33), (128, 45), (32, 2), (19, 306), (10, 166), (6, 32)]
    (codeMat 85) (codeMat 87) (codeMat 468) true
    det85 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0883_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0883_orbit
  simpa only [lower55] using h

theorem space0884_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [256, 130, 32, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(256, 1), (130, 45), (32, 2), (19, 306), (10, 166), (6, 32)]
    (codeMat 84) (codeMat 87) (codeMat 468) true
    det84 det87 inv87
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0884_lower : 14 ≤ frozenWangTable.L0 (spanCodes [256, 130, 32, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0884_orbit
  simpa only [lower55] using h

theorem space0885_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 129, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 138), (129, 139), (34, 34), (19, 166), (10, 404), (6, 2)]
    (codeMat 204) (codeMat 115) (codeMat 492) true
    det204 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0885_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0885_orbit
  simpa only [lower55] using h

theorem space0886_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [322, 194, 34, 19, 10, 6]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(322, 136), (194, 139), (34, 436), (19, 306), (10, 404), (6, 2)]
    (codeMat 141) (codeMat 501) (codeMat 494) true
    det141 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0886_lower : 14 ≤ frozenWangTable.L0 (spanCodes [322, 194, 34, 19, 10, 6]) := by
  have h := frozenWangTable.lower_le_L0 55 space0886_orbit
  simpa only [lower55] using h

theorem space0887_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [257, 129, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(257, 440), (129, 441), (35, 406), (19, 404), (10, 166), (7, 438)]
    (codeMat 212) (codeMat 122) (codeMat 460) true
    det212 det122 inv122
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0887_lower : 14 ≤ frozenWangTable.L0 (spanCodes [257, 129, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0887_orbit
  simpa only [lower55] using h

theorem space0888_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 130, 35, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 46), (130, 45), (35, 406), (19, 404), (10, 166), (7, 438)]
    (codeMat 214) (codeMat 122) (codeMat 460) true
    det214 det122 inv122
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0888_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 130, 35, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0888_orbit
  simpa only [lower55] using h

theorem space0889_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 440), (131, 441), (32, 32), (19, 404), (10, 306), (5, 438)]
    (codeMat 156) (codeMat 115) (codeMat 492) true
    det156 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0889_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0889_orbit
  simpa only [lower55] using h

theorem space0890_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [321, 193, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(321, 284), (193, 287), (32, 438), (19, 404), (10, 166), (5, 32)]
    (codeMat 95) (codeMat 501) (codeMat 494) true
    det95 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0890_lower : 14 ≤ frozenWangTable.L0 (spanCodes [321, 193, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0890_orbit
  simpa only [lower55] using h

theorem space0891_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [323, 195, 32, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(323, 44), (195, 45), (32, 438), (19, 404), (10, 166), (5, 32)]
    (codeMat 92) (codeMat 501) (codeMat 494) true
    det92 det501 inv501
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0891_lower : 14 ≤ frozenWangTable.L0 (spanCodes [323, 195, 32, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0891_orbit
  simpa only [lower55] using h

theorem space0892_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [323, 192, 35, 19, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(323, 12), (192, 45), (35, 164), (19, 166), (10, 404), (5, 32)]
    (codeMat 85) (codeMat 458) (codeMat 458) true
    det85 det458 inv458
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0892_lower : 14 ≤ frozenWangTable.L0 (spanCodes [323, 192, 35, 19, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 55 space0892_orbit
  simpa only [lower55] using h

theorem space0893_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [259, 131, 33, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(259, 284), (131, 287), (33, 272), (19, 306), (10, 404), (4, 32)]
    (codeMat 95) (codeMat 122) (codeMat 460) true
    det95 det122 inv122
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0893_lower : 14 ≤ frozenWangTable.L0 (spanCodes [259, 131, 33, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0893_orbit
  simpa only [lower55] using h

theorem space0894_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [258, 128, 35, 19, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(258, 12), (128, 45), (35, 304), (19, 306), (10, 166), (4, 32)]
    (codeMat 85) (codeMat 115) (codeMat 492) true
    det85 det115 inv115
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0894_lower : 14 ≤ frozenWangTable.L0 (spanCodes [258, 128, 35, 19, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 55 space0894_orbit
  simpa only [lower55] using h

theorem space0895_orbit :
    frozenWangTable.OrbitImage 55 (spanCodes [323, 195, 34, 19, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 55 [(323, 46), (195, 45), (34, 134), (19, 306), (10, 166), (7, 438)]
    (codeMat 159) (codeMat 458) (codeMat 458) true
    det159 det458 inv458
    (by rw [basis55]; decide +kernel)
    (by rw [basis55]; decide +kernel)

theorem space0895_lower : 14 ≤ frozenWangTable.L0 (spanCodes [323, 195, 34, 19, 10, 7]) := by
  have h := frozenWangTable.lower_le_L0 55 space0895_orbit
  simpa only [lower55] using h


end QiushiMatmul.FrozenWang
