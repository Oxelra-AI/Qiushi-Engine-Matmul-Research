import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space2144_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [133, 68, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(133, 132), (68, 166), (16, 1), (8, 9), (2, 2)]
    (codeMat 330) (codeMat 299) (codeMat 318) true
    det330 det299 inv299
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2144_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 68, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 103 space2144_orbit
  simpa only [lower103] using h

theorem space2145_orbit :
    frozenWangTable.OrbitImage 141 (spanCodes [130, 68, 35, 18, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 141 [(130, 2), (68, 383), (35, 296), (18, 1), (10, 33)]
    (codeMat 171) (codeMat 267) (codeMat 282) true
    det171 det267 inv267
    (by rw [basis141]; decide +kernel)
    (by rw [basis141]; decide +kernel)

theorem space2145_lower : 15 ≤ frozenWangTable.L0 (spanCodes [130, 68, 35, 18, 10]) := by
  have h := frozenWangTable.lower_le_L0 141 space2145_orbit
  simpa only [lower141] using h

theorem space2146_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [160, 68, 16, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    det266 det266 inv266
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2146_lower : 15 ≤ frozenWangTable.L0 (spanCodes [160, 68, 16, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 29 space2146_orbit
  simpa only [lower29] using h

theorem space2147_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [133, 68, 33, 16, 8, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(133, 96), (68, 232), (33, 30), (16, 1), (8, 3), (2, 8)]
    (codeMat 330) (codeMat 299) (codeMat 318) false
    det330 det299 inv299
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2147_lower : 15 ≤ frozenWangTable.L0 (spanCodes [133, 68, 33, 16, 8, 2]) := by
  have h := frozenWangTable.lower_le_L0 35 space2147_orbit
  simpa only [lower35] using h

theorem space2148_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 65, 32, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 10), (65, 9), (32, 32), (10, 164), (5, 2)]
    (codeMat 141) (codeMat 169) (codeMat 225) true
    det141 det169 inv169
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2148_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 65, 32, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space2148_orbit
  simpa only [lower103] using h

theorem space2149_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 65, 33, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 10), (65, 9), (33, 34), (10, 166), (5, 2)]
    (codeMat 205) (codeMat 185) (codeMat 481) true
    det205 det185 inv185
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2149_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 65, 33, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space2149_orbit
  simpa only [lower103] using h

theorem space2150_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 64, 34, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 82), (64, 2), (34, 100), (10, 68), (4, 9), (1, 1)]
    (codeMat 161) (codeMat 165) (codeMat 163) true
    det161 det165 inv165
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2150_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 64, 34, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2150_orbit
  simpa only [lower31] using h

theorem space2151_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 64, 35, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 1), (64, 9), (35, 132), (10, 166), (4, 2)]
    (codeMat 204) (codeMat 157) (codeMat 486) true
    det204 det157 inv157
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2151_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 64, 35, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space2151_orbit
  simpa only [lower103] using h

theorem space2152_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 64, 32, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 80), (64, 2), (32, 32), (10, 68), (4, 8), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    det161 det161 inv161
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2152_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 64, 32, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2152_orbit
  simpa only [lower31] using h

theorem space2153_orbit :
    frozenWangTable.OrbitImage 220 (spanCodes [288, 161, 68, 9, 3]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 220 [(288, 16), (161, 334), (68, 209), (9, 192), (3, 36)]
    (codeMat 247) (codeMat 187) (codeMat 229) false
    det247 det187 inv187
    (by rw [basis220]; decide +kernel)
    (by rw [basis220]; decide +kernel)

theorem space2153_lower : 15 ≤ frozenWangTable.L0 (spanCodes [288, 161, 68, 9, 3]) := by
  have h := frozenWangTable.lower_le_L0 220 space2153_orbit
  simpa only [lower220] using h

theorem space2154_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 128, 65, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 10), (128, 32), (65, 2), (10, 164), (5, 9)]
    (codeMat 165) (codeMat 172) (codeMat 99) false
    det165 det172 inv172
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2154_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space2154_orbit
  simpa only [lower103] using h

theorem space2155_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [257, 129, 65, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(257, 10), (129, 34), (65, 2), (10, 164), (5, 9)]
    (codeMat 229) (codeMat 188) (codeMat 103) false
    det229 det188 inv188
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2155_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 103 space2155_orbit
  simpa only [lower103] using h

theorem space2156_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 130, 64, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 52), (130, 54), (64, 1), (10, 112), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 401) (codeMat 401) false
    det140 det401 inv401
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2156_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 64, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2156_orbit
  simpa only [lower31] using h

theorem space2157_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 130, 64, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 1), (130, 32), (64, 2), (10, 164), (4, 9)]
    (codeMat 172) (codeMat 140) (codeMat 98) false
    det172 det140 inv140
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2157_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space2157_orbit
  simpa only [lower103] using h

theorem space2158_orbit :
    frozenWangTable.OrbitImage 103 (spanCodes [256, 131, 64, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 103 [(256, 1), (131, 34), (64, 2), (10, 164), (4, 9)]
    (codeMat 236) (codeMat 156) (codeMat 102) false
    det236 det156 inv156
    (by rw [basis103]; decide +kernel)
    (by rw [basis103]; decide +kernel)

theorem space2158_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 103 space2158_orbit
  simpa only [lower103] using h

theorem space2159_orbit :
    frozenWangTable.OrbitImage 31 (spanCodes [258, 128, 64, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 31 [(258, 20), (128, 2), (64, 1), (10, 80), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    det140 det273 inv273
    (by rw [basis31]; decide +kernel)
    (by rw [basis31]; decide +kernel)

theorem space2159_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 64, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 31 space2159_orbit
  simpa only [lower31] using h

theorem space2160_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [276, 132, 68, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(276, 246), (132, 30), (68, 22), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    det161 det314 inv314
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2160_lower : 15 ≤ frozenWangTable.L0 (spanCodes [276, 132, 68, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 35 space2160_orbit
  simpa only [lower35] using h

theorem space2161_orbit :
    frozenWangTable.OrbitImage 141 (spanCodes [260, 128, 68, 33, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 141 [(260, 32), (128, 2), (68, 33), (33, 265), (10, 383)]
    (codeMat 236) (codeMat 337) (codeMat 337) false
    det236 det337 inv337
    (by rw [basis141]; decide +kernel)
    (by rw [basis141]; decide +kernel)

theorem space2161_lower : 15 ≤ frozenWangTable.L0 (spanCodes [260, 128, 68, 33, 10]) := by
  have h := frozenWangTable.lower_le_L0 141 space2161_orbit
  simpa only [lower141] using h

theorem space2162_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [256, 160, 64, 10, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(256, 1), (160, 68), (64, 2), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    det140 det140 inv140
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2162_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 160, 64, 10, 4, 1]) := by
  have h := frozenWangTable.lower_le_L0 29 space2162_orbit
  simpa only [lower29] using h

theorem space2163_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 129, 64, 35, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (129, 30), (64, 3), (35, 96), (10, 232), (4, 8)]
    (codeMat 204) (codeMat 157) (codeMat 486) false
    det204 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2163_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 35, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2163_orbit
  simpa only [lower35] using h

theorem space2164_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 131, 64, 33, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (131, 139), (64, 9), (33, 31), (10, 252), (4, 3)]
    (codeMat 172) (codeMat 157) (codeMat 486) true
    det172 det157 inv157
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2164_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 131, 64, 33, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2164_orbit
  simpa only [lower35] using h

theorem space2165_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 129, 65, 35, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 11), (129, 139), (65, 9), (35, 227), (10, 252), (5, 3)]
    (codeMat 165) (codeMat 185) (codeMat 481) true
    det165 det185 inv185
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2165_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 129, 65, 35, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2165_orbit
  simpa only [lower35] using h

theorem space2166_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [257, 128, 65, 35, 10, 5]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(257, 10), (128, 128), (65, 8), (35, 252), (10, 224), (5, 3)]
    (codeMat 165) (codeMat 172) (codeMat 99) true
    det165 det172 inv172
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2166_lower : 15 ≤ frozenWangTable.L0 (spanCodes [257, 128, 65, 35, 10, 5]) := by
  have h := frozenWangTable.lower_le_L0 35 space2166_orbit
  simpa only [lower35] using h

theorem space2167_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 129, 64, 34, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (129, 28), (64, 3), (34, 96), (10, 224), (4, 8)]
    (codeMat 140) (codeMat 141) (codeMat 226) false
    det140 det141 inv141
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2167_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 129, 64, 34, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2167_orbit
  simpa only [lower35] using h

theorem space2168_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [256, 130, 64, 33, 10, 4]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(256, 1), (130, 128), (64, 8), (33, 28), (10, 224), (4, 3)]
    (codeMat 172) (codeMat 140) (codeMat 98) true
    det172 det140 inv140
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2168_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 130, 64, 33, 10, 4]) := by
  have h := frozenWangTable.lower_le_L0 35 space2168_orbit
  simpa only [lower35] using h

theorem space2169_orbit :
    frozenWangTable.OrbitImage 29 (spanCodes [256, 128, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 29 [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    det84 det84 inv84
    (by rw [basis29]; decide +kernel)
    (by rw [basis29]; decide +kernel)

theorem space2169_lower : 15 ≤ frozenWangTable.L0 (spanCodes [256, 128, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 29 space2169_orbit
  simpa only [lower29] using h

theorem space2170_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 130, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 136), (130, 128), (68, 232), (32, 3), (16, 2), (10, 150)]
    (codeMat 354) (codeMat 124) (codeMat 124) false
    det354 det124 inv124
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2170_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 130, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2170_orbit
  simpa only [lower35] using h

theorem space2171_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 134, 68, 32, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 31), (134, 28), (68, 252), (32, 9), (16, 8), (10, 104)]
    (codeMat 114) (codeMat 124) (codeMat 124) true
    det114 det124 inv124
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2171_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 134, 68, 32, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2171_orbit
  simpa only [lower35] using h

theorem space2172_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 128, 68, 34, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 31), (128, 3), (68, 252), (34, 22), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 110) (codeMat 444) true
    det86 det110 inv110
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2172_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 128, 68, 34, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2172_orbit
  simpa only [lower35] using h

theorem space2173_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [262, 128, 68, 38, 16, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(262, 139), (128, 9), (68, 252), (38, 136), (16, 8), (10, 104)]
    (codeMat 214) (codeMat 102) (codeMat 156) false
    det214 det102 inv102
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2173_lower : 15 ≤ frozenWangTable.L0 (spanCodes [262, 128, 68, 38, 16, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2173_orbit
  simpa only [lower35] using h

theorem space2174_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [263, 135, 68, 33, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(263, 126), (135, 252), (68, 245), (33, 232), (17, 104), (10, 96)]
    (codeMat 158) (codeMat 481) (codeMat 185) false
    det158 det481 inv481
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2174_lower : 15 ≤ frozenWangTable.L0 (spanCodes [263, 135, 68, 33, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2174_orbit
  simpa only [lower35] using h

theorem space2175_orbit :
    frozenWangTable.OrbitImage 35 (spanCodes [258, 135, 68, 36, 17, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 35 [(258, 224), (135, 252), (68, 255), (36, 128), (17, 148), (10, 150)]
    (codeMat 94) (codeMat 473) (codeMat 409) true
    det94 det473 inv473
    (by rw [basis35]; decide +kernel)
    (by rw [basis35]; decide +kernel)

theorem space2175_lower : 15 ≤ frozenWangTable.L0 (spanCodes [258, 135, 68, 36, 17, 10]) := by
  have h := frozenWangTable.lower_le_L0 35 space2175_orbit
  simpa only [lower35] using h


end QiushiMatmul.FrozenWang
