import QiushiFrozenWangChecks

-- Generated numeric bindings; no tensor-rank or pickle theorem.
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace QiushiMatmul.FrozenWang

theorem space3872_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [258, 130, 66, 34, 16, 10, 6, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(258, 327), (130, 325), (66, 326), (34, 376), (16, 40), (10, 368), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 494) (codeMat 501) false
    det84 det494 inv494
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3872_lower : 9 ≤ frozenWangTable.L0 (spanCodes [258, 130, 66, 34, 16, 10, 6, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3872_orbit
  simpa only [lower3] using h

theorem space3873_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [257, 129, 64, 33, 16, 8, 5, 2]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(257, 71), (129, 68), (64, 1), (33, 120), (16, 32), (8, 8), (5, 384), (2, 256)]
    (codeMat 84) (codeMat 421) (codeMat 179) false
    det84 det421 inv421
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3873_lower : 9 ≤ frozenWangTable.L0 (spanCodes [257, 129, 64, 33, 16, 8, 5, 2]) := by
  have h := frozenWangTable.lower_le_L0 3 space3873_orbit
  simpa only [lower3] using h

theorem space3874_orbit :
    frozenWangTable.OrbitImage 3 (spanCodes [260, 132, 68, 32, 20, 8, 2, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 3 [(260, 325), (132, 326), (68, 324), (32, 40), (20, 368), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 468) (codeMat 87) false
    det84 det468 inv468
    (by rw [basis3]; decide +kernel)
    (by rw [basis3]; decide +kernel)

theorem space3874_lower : 9 ≤ frozenWangTable.L0 (spanCodes [260, 132, 68, 32, 20, 8, 2, 1]) := by
  have h := frozenWangTable.lower_le_L0 3 space3874_orbit
  simpa only [lower3] using h

theorem space3875_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [163, 84, 11]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(163, 250), (84, 84), (11, 10)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    det401 det275 inv275
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3875_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 11]) := by
  have h := frozenWangTable.lower_le_L0 468 space3875_orbit
  simpa only [lower468] using h

theorem space3876_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [163, 84, 12]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(163, 106), (84, 165), (12, 96)]
    (codeMat 107) (codeMat 354) (codeMat 142) true
    det107 det354 inv354
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3876_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 12]) := by
  have h := frozenWangTable.lower_le_L0 475 space3876_orbit
  simpa only [lower475] using h

theorem space3877_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [163, 84, 13]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(163, 94), (84, 303), (13, 293)]
    (codeMat 314) (codeMat 277) (codeMat 277) false
    det314 det277 inv277
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3877_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 13]) := by
  have h := frozenWangTable.lower_le_L0 473 space3877_orbit
  simpa only [lower473] using h

theorem space3878_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [163, 84, 14]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(163, 106), (84, 372), (14, 96)]
    (codeMat 95) (codeMat 372) (codeMat 93) false
    det95 det372 inv372
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3878_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 14]) := by
  have h := frozenWangTable.lower_le_L0 476 space3878_orbit
  simpa only [lower476] using h

theorem space3879_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [163, 84, 15]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(163, 250), (84, 84), (15, 164)]
    (codeMat 230) (codeMat 206) (codeMat 498) false
    det230 det206 inv206
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3879_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 84, 15]) := by
  have h := frozenWangTable.lower_le_L0 468 space3879_orbit
  simpa only [lower468] using h

theorem space3880_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [163, 69, 17]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(163, 174), (69, 240), (17, 10)]
    (codeMat 331) (codeMat 313) (codeMat 313) false
    det331 det313 inv313
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3880_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 69, 17]) := by
  have h := frozenWangTable.lower_le_L0 468 space3880_orbit
  simpa only [lower468] using h

theorem space3881_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [163, 71, 19]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(163, 207), (71, 96), (19, 10)]
    (codeMat 345) (codeMat 270) (codeMat 298) true
    det345 det270 inv270
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3881_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 71, 19]) := by
  have h := frozenWangTable.lower_le_L0 475 space3881_orbit
  simpa only [lower475] using h

theorem space3882_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [163, 66, 22]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(163, 94), (66, 293), (22, 10)]
    (codeMat 409) (codeMat 98) (codeMat 140) false
    det409 det98 inv98
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3882_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 66, 22]) := by
  have h := frozenWangTable.lower_le_L0 473 space3882_orbit
  simpa only [lower473] using h

theorem space3883_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [163, 67, 23]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(163, 106), (67, 96), (23, 197)]
    (codeMat 98) (codeMat 226) (codeMat 141) false
    det98 det226 inv226
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3883_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 67, 23]) := by
  have h := frozenWangTable.lower_le_L0 475 space3883_orbit
  simpa only [lower475] using h

theorem space3884_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [163, 77, 25]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(163, 106), (77, 175), (25, 10)]
    (codeMat 339) (codeMat 302) (codeMat 302) false
    det339 det302 inv302
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3884_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 77, 25]) := by
  have h := frozenWangTable.lower_le_L0 475 space3884_orbit
  simpa only [lower475] using h

theorem space3885_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [163, 78, 26]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(163, 84), (78, 164), (26, 10)]
    (codeMat 474) (codeMat 302) (codeMat 302) false
    det474 det302 inv302
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3885_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 78, 26]) := by
  have h := frozenWangTable.lower_le_L0 468 space3885_orbit
  simpa only [lower468] using h

theorem space3886_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [163, 74, 30]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(163, 250), (74, 164), (30, 240)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    det93 det372 inv372
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3886_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 74, 30]) := by
  have h := frozenWangTable.lower_le_L0 468 space3886_orbit
  simpa only [lower468] using h

theorem space3887_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [163, 75, 31]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(163, 106), (75, 96), (31, 276)]
    (codeMat 86) (codeMat 500) (codeMat 94) true
    det86 det500 inv500
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3887_lower : 18 ≤ frozenWangTable.L0 (spanCodes [163, 75, 31]) := by
  have h := frozenWangTable.lower_le_L0 476 space3887_orbit
  simpa only [lower476] using h

theorem space3888_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [129, 84, 34]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(129, 240), (84, 174), (34, 164)]
    (codeMat 103) (codeMat 409) (codeMat 473) false
    det103 det409 inv409
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3888_lower : 18 ≤ frozenWangTable.L0 (spanCodes [129, 84, 34]) := by
  have h := frozenWangTable.lower_le_L0 468 space3888_orbit
  simpa only [lower468] using h

theorem space3889_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [134, 84, 37]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(134, 10), (84, 165), (37, 96)]
    (codeMat 141) (codeMat 85) (codeMat 340) false
    det141 det85 inv85
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3889_lower : 18 ≤ frozenWangTable.L0 (spanCodes [134, 84, 37]) := by
  have h := frozenWangTable.lower_le_L0 475 space3889_orbit
  simpa only [lower475] using h

theorem space3890_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [133, 84, 38]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(133, 276), (84, 286), (38, 96)]
    (codeMat 107) (codeMat 281) (codeMat 281) true
    det107 det281 inv281
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3890_lower : 18 ≤ frozenWangTable.L0 (spanCodes [133, 84, 38]) := by
  have h := frozenWangTable.lower_le_L0 476 space3890_orbit
  simpa only [lower476] using h

theorem space3891_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [132, 84, 39]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(132, 10), (84, 250), (39, 164)]
    (codeMat 165) (codeMat 115) (codeMat 492) false
    det165 det115 inv115
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3891_lower : 18 ≤ frozenWangTable.L0 (spanCodes [132, 84, 39]) := by
  have h := frozenWangTable.lower_le_L0 468 space3891_orbit
  simpa only [lower468] using h

theorem space3892_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [138, 84, 41]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(138, 164), (84, 174), (41, 240)]
    (codeMat 142) (codeMat 460) (codeMat 122) false
    det142 det460 inv460
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3892_lower : 18 ≤ frozenWangTable.L0 (spanCodes [138, 84, 41]) := by
  have h := frozenWangTable.lower_le_L0 468 space3892_orbit
  simpa only [lower468] using h

theorem space3893_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [137, 84, 42]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(137, 197), (84, 207), (42, 96)]
    (codeMat 177) (codeMat 485) (codeMat 171) true
    det177 det485 inv485
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3893_lower : 18 ≤ frozenWangTable.L0 (spanCodes [137, 84, 42]) := by
  have h := frozenWangTable.lower_le_L0 475 space3893_orbit
  simpa only [lower475] using h

theorem space3894_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [136, 84, 43]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(136, 175), (84, 106), (43, 96)]
    (codeMat 95) (codeMat 442) (codeMat 334) false
    det95 det442 inv442
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3894_lower : 18 ≤ frozenWangTable.L0 (spanCodes [136, 84, 43]) := by
  have h := frozenWangTable.lower_le_L0 475 space3894_orbit
  simpa only [lower475] using h

theorem space3895_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [141, 84, 46]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(141, 84), (84, 94), (46, 293)]
    (codeMat 305) (codeMat 314) (codeMat 271) false
    det305 det314 inv314
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3895_lower : 18 ≤ frozenWangTable.L0 (spanCodes [141, 84, 46]) := by
  have h := frozenWangTable.lower_le_L0 473 space3895_orbit
  simpa only [lower473] using h

theorem space3896_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [145, 84, 50]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(145, 276), (84, 286), (50, 96)]
    (codeMat 141) (codeMat 460) (codeMat 122) false
    det141 det460 inv460
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3896_lower : 18 ≤ frozenWangTable.L0 (spanCodes [145, 84, 50]) := by
  have h := frozenWangTable.lower_le_L0 476 space3896_orbit
  simpa only [lower476] using h

theorem space3897_orbit :
    frozenWangTable.OrbitImage 475 (spanCodes [150, 84, 53]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 475 [(150, 175), (84, 106), (53, 96)]
    (codeMat 250) (codeMat 167) (codeMat 167) true
    det250 det167 inv167
    (by rw [basis475]; decide +kernel)
    (by rw [basis475]; decide +kernel)

theorem space3897_lower : 18 ≤ frozenWangTable.L0 (spanCodes [150, 84, 53]) := by
  have h := frozenWangTable.lower_le_L0 475 space3897_orbit
  simpa only [lower475] using h

theorem space3898_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [154, 84, 57]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(154, 96), (84, 286), (57, 276)]
    (codeMat 159) (codeMat 140) (codeMat 98) true
    det159 det140 inv140
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3898_lower : 18 ≤ frozenWangTable.L0 (spanCodes [154, 84, 57]) := by
  have h := frozenWangTable.lower_le_L0 476 space3898_orbit
  simpa only [lower476] using h

theorem space3899_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [153, 84, 58]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(153, 10), (84, 369), (58, 293)]
    (codeMat 299) (codeMat 303) (codeMat 286) false
    det299 det303 inv303
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3899_lower : 18 ≤ frozenWangTable.L0 (spanCodes [153, 84, 58]) := by
  have h := frozenWangTable.lower_le_L0 473 space3899_orbit
  simpa only [lower473] using h

theorem space3900_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [152, 84, 59]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(152, 293), (84, 379), (59, 10)]
    (codeMat 346) (codeMat 225) (codeMat 169) false
    det346 det225 inv225
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3900_lower : 18 ≤ frozenWangTable.L0 (spanCodes [152, 84, 59]) := by
  have h := frozenWangTable.lower_le_L0 473 space3900_orbit
  simpa only [lower473] using h

theorem space3901_orbit :
    frozenWangTable.OrbitImage 476 (spanCodes [159, 84, 60]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 476 [(159, 382), (84, 106), (60, 96)]
    (codeMat 214) (codeMat 156) (codeMat 102) false
    det214 det156 inv156
    (by rw [basis476]; decide +kernel)
    (by rw [basis476]; decide +kernel)

theorem space3901_lower : 18 ≤ frozenWangTable.L0 (spanCodes [159, 84, 60]) := by
  have h := frozenWangTable.lower_le_L0 476 space3901_orbit
  simpa only [lower476] using h

theorem space3902_orbit :
    frozenWangTable.OrbitImage 468 (spanCodes [158, 84, 61]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 468 [(158, 94), (84, 250), (61, 240)]
    (codeMat 215) (codeMat 156) (codeMat 102) false
    det215 det156 inv156
    (by rw [basis468]; decide +kernel)
    (by rw [basis468]; decide +kernel)

theorem space3902_lower : 18 ≤ frozenWangTable.L0 (spanCodes [158, 84, 61]) := by
  have h := frozenWangTable.lower_le_L0 468 space3902_orbit
  simpa only [lower468] using h

theorem space3903_orbit :
    frozenWangTable.OrbitImage 473 (spanCodes [157, 84, 62]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 473 [(157, 379), (84, 94), (62, 10)]
    (codeMat 339) (codeMat 423) (codeMat 181) false
    det339 det423 inv423
    (by rw [basis473]; decide +kernel)
    (by rw [basis473]; decide +kernel)

theorem space3903_lower : 18 ≤ frozenWangTable.L0 (spanCodes [157, 84, 62]) := by
  have h := frozenWangTable.lower_le_L0 473 space3903_orbit
  simpa only [lower473] using h


end QiushiMatmul.FrozenWang
