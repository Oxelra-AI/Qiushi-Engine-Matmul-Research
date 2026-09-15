import FrozenRegistry.Bridge

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace QiushiMatmul.FrozenRegistry.Transport

theorem orbit090 :
    frozenWangTable.OrbitImage 90 (spanCodes [256, 128, 64, 35, 16]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 90 [(256, 4), (128, 1), (64, 3), (35, 160), (16, 8)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 90 = [160, 8, 4, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 90 = [160, 8, 4, 2, 1] by decide]; decide)

theorem bound090 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 90))
      (frozenWangTable.lower 90) := by
  have h := QiushiMatmul.plane491GenBound0522
  change QuotientRankAtLeast (spanCodes [256, 128, 64, 35, 16, 4]) 12 at h
  have htarget := bind_contained [256, 128, 64, 35, 16] [256, 128, 64, 35, 16, 4]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 90 orbit090 htarget (by decide)

theorem orbit091 :
    frozenWangTable.OrbitImage 91 (spanCodes [256, 128, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 91 [(256, 4), (128, 1), (64, 2), (19, 200), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 91 = [152, 80, 4, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 91 = [152, 80, 4, 2, 1] by decide]; decide)

theorem bound091 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 91))
      (frozenWangTable.lower 91) := by
  have h := QiushiMatmul.plane490GenBound0459
  change QuotientRankAtLeast (spanCodes [256, 128, 64, 16, 9, 3]) 12 at h
  have htarget := bind_contained [256, 128, 64, 19, 10] [256, 128, 64, 16, 9, 3]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 91 orbit091 htarget (by decide)

theorem orbit122 :
    frozenWangTable.OrbitImage 122 (spanCodes [259, 128, 64, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 122 [(259, 196), (128, 1), (64, 2), (19, 200), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 122 = [148, 80, 12, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 122 = [148, 80, 12, 2, 1] by decide]; decide)

theorem bound122 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 122))
      (frozenWangTable.lower 122) := by
  have h := QiushiMatmul.plane484GenBound0329
  change QuotientRankAtLeast (spanCodes [257, 128, 64, 17, 8, 2]) 15 at h
  have htarget := bind_contained [259, 128, 64, 19, 10] [257, 128, 64, 17, 8, 2]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 122 orbit122 htarget (by decide)

theorem orbit136 :
    frozenWangTable.OrbitImage 136 (spanCodes [256, 192, 38, 22, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 136 [(256, 1), (192, 2), (38, 264), (22, 296), (10, 376)]
    (codeMat 84) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 136 = [264, 80, 32, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 136 = [264, 80, 32, 2, 1] by decide]; decide)

theorem bound136 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 136))
      (frozenWangTable.lower 136) := by
  have h := QiushiMatmul.plane468GenBound0157
  change QuotientRankAtLeast (spanCodes [256, 130, 66, 38, 22, 10]) 14 at h
  have htarget := bind_contained [256, 192, 38, 22, 10] [256, 130, 66, 38, 22, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 136 orbit136 htarget (by decide)

theorem orbit139 :
    frozenWangTable.OrbitImage 139 (spanCodes [256, 128, 33, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 139 [(256, 3), (128, 1), (33, 408), (19, 456), (10, 112)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 139 = [408, 80, 32, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 139 = [408, 80, 32, 2, 1] by decide]; decide)

theorem bound139 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 139))
      (frozenWangTable.lower 139) := by
  have h := QiushiMatmul.plane490GenBound0418
  change QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 19, 10]) 14 at h
  have htarget := bind_contained [256, 128, 33, 19, 10] [256, 128, 65, 33, 19, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 139 orbit139 htarget (by decide)

theorem orbit154 :
    frozenWangTable.OrbitImage 154 (spanCodes [418, 67, 18, 10, 7]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 154 [(418, 315), (67, 97), (18, 288), (10, 96), (7, 16)]
    (codeMat 143) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 154 = [288, 96, 16, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 154 = [288, 96, 16, 10, 1] by decide]; decide)

theorem bound154 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 154))
      (frozenWangTable.lower 154) := by
  have h := QiushiMatmul.plane462GenBound0111
  change QuotientRankAtLeast (spanCodes [258, 160, 67, 18, 10, 7]) 14 at h
  have htarget := bind_contained [418, 67, 18, 10, 7] [258, 160, 67, 18, 10, 7]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 154 orbit154 htarget (by decide)

theorem orbit170 :
    frozenWangTable.OrbitImage 170 (spanCodes [260, 156, 86, 54, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 170 [(260, 1), (156, 431), (86, 314), (54, 432), (1, 128)]
    (codeMat 85) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 170 = [292, 128, 20, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 170 = [292, 128, 20, 10, 1] by decide]; decide)

theorem bound170 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 170))
      (frozenWangTable.lower 170) := by
  have h := QiushiMatmul.plane315GenBound0024
  change QuotientRankAtLeast (spanCodes [260, 150, 86, 54, 10, 1]) 14 at h
  have htarget := bind_contained [260, 156, 86, 54, 1] [260, 150, 86, 54, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 170 orbit170 htarget (by decide)

theorem orbit172 :
    frozenWangTable.OrbitImage 172 (spanCodes [272, 162, 80, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 172 [(272, 21), (162, 170), (80, 20), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 172 = [256, 160, 20, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 172 = [256, 160, 20, 10, 1] by decide]; decide)

theorem bound172 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 172))
      (frozenWangTable.lower 172) := by
  have h := QiushiMatmul.plane426GenBound0143
  change QuotientRankAtLeast (spanCodes [272, 148, 80, 54, 10, 1]) 15 at h
  have htarget := bind_contained [272, 162, 80, 10, 1] [272, 148, 80, 54, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 172 orbit172 htarget (by decide)

theorem orbit173 :
    frozenWangTable.OrbitImage 173 (spanCodes [269, 136, 69, 41, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 173 [(269, 278), (136, 21), (69, 258), (41, 160), (20, 424)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 173 = [258, 160, 20, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 173 = [258, 160, 20, 10, 1] by decide]; decide)

theorem bound173 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 173))
      (frozenWangTable.lower 173) := by
  have h := QiushiMatmul.plane456GenBound0104
  change QuotientRankAtLeast (spanCodes [263, 130, 69, 35, 20, 10]) 15 at h
  have htarget := bind_contained [269, 136, 69, 41, 20] [263, 130, 69, 35, 20, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 173 orbit173 htarget (by decide)

theorem orbit200 :
    frozenWangTable.OrbitImage 200 (spanCodes [272, 132, 80, 50, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 200 [(272, 42), (132, 133), (80, 43), (50, 376), (10, 344)]
    (codeMat 84) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 200 = [338, 132, 32, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 200 = [338, 132, 32, 10, 1] by decide]; decide)

theorem bound200 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 200))
      (frozenWangTable.lower 200) := by
  have h := QiushiMatmul.plane426GenBound0129
  change QuotientRankAtLeast (spanCodes [272, 132, 80, 50, 10, 1]) 15 at h
  have htarget := bind_contained [272, 132, 80, 50, 10] [272, 132, 80, 50, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 200 orbit200 htarget (by decide)

theorem orbit205 :
    frozenWangTable.OrbitImage 205 (spanCodes [265, 129, 64, 47, 20]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 205 [(265, 79), (129, 68), (64, 1), (47, 176), (20, 480)]
    (codeMat 84) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 205 = [276, 176, 68, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 205 = [276, 176, 68, 10, 1] by decide]; decide)

theorem bound205 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 205))
      (frozenWangTable.lower 205) := by
  have h := QiushiMatmul.plane474GenBound0033
  change QuotientRankAtLeast (spanCodes [259, 129, 64, 37, 20, 10]) 16 at h
  have htarget := bind_contained [265, 129, 64, 47, 20] [259, 129, 64, 37, 20, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 205 orbit205 htarget (by decide)

theorem orbit222 :
    frozenWangTable.OrbitImage 222 (spanCodes [277, 146, 68, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 222 [(277, 403), (146, 1), (68, 374), (48, 16), (10, 112)]
    (codeMat 87) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 222 = [262, 132, 96, 16, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 222 = [262, 132, 96, 16, 1] by decide]; decide)

theorem bound222 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 222))
      (frozenWangTable.lower 222) := by
  have h := QiushiMatmul.plane464GenBound0092
  change QuotientRankAtLeast (spanCodes [259, 132, 68, 38, 22, 10]) 15 at h
  have htarget := bind_contained [277, 146, 68, 48, 10] [259, 132, 68, 38, 22, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 222 orbit222 htarget (by decide)

theorem orbit226 :
    frozenWangTable.OrbitImage 226 (spanCodes [264, 129, 73, 33, 29]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 226 [(264, 113), (129, 96), (73, 1), (33, 447), (29, 237)]
    (codeMat 103) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 226 = [290, 140, 96, 16, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 226 = [290, 140, 96, 16, 1] by decide]; decide)

theorem bound226 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 226))
      (frozenWangTable.lower 226) := by
  have h := QiushiMatmul.plane469GenBound0107
  change QuotientRankAtLeast (spanCodes [258, 129, 67, 33, 23, 10]) 15 at h
  have htarget := bind_contained [264, 129, 73, 33, 29] [258, 129, 67, 33, 23, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 226 orbit226 htarget (by decide)

theorem orbit230 :
    frozenWangTable.OrbitImage 230 (spanCodes [275, 128, 87, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 230 [(275, 459), (128, 1), (87, 270), (48, 16), (10, 112)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 230 = [270, 164, 96, 16, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 230 = [270, 164, 96, 16, 1] by decide]; decide)

theorem bound230 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 230))
      (frozenWangTable.lower 230) := by
  have h := QiushiMatmul.plane476GenBound0070
  change QuotientRankAtLeast (spanCodes [275, 128, 80, 48, 10, 7]) 15 at h
  have htarget := bind_contained [275, 128, 87, 48, 10] [275, 128, 80, 48, 10, 7]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 230 orbit230 htarget (by decide)

theorem orbit271 :
    frozenWangTable.OrbitImage 271 (spanCodes [256, 64, 48, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 271 [(256, 1), (64, 2), (48, 32), (10, 336)]
    (codeMat 84) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 271 = [336, 32, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 271 = [336, 32, 2, 1] by decide]; decide)

theorem bound271 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 271))
      (frozenWangTable.lower 271) := by
  have h := QiushiMatmul.plane488GenBound0240
  change QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 10]) 15 at h
  have htarget := bind_contained [256, 64, 48, 10] [256, 132, 64, 32, 16, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 271 orbit271 htarget (by decide)

theorem orbit277 :
    frozenWangTable.OrbitImage 277 (spanCodes [256, 128, 19, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 277 [(256, 2), (128, 1), (19, 328), (10, 96)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 277 = [296, 96, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 277 = [296, 96, 2, 1] by decide]; decide)

theorem bound277 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 277))
      (frozenWangTable.lower 277) := by
  have h := QiushiMatmul.plane484GenBound0349
  change QuotientRankAtLeast (spanCodes [256, 128, 69, 19, 10]) 15 at h
  have htarget := bind_contained [256, 128, 19, 10] [256, 128, 69, 19, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 277 orbit277 htarget (by decide)

theorem orbit313 :
    frozenWangTable.OrbitImage 313 (spanCodes [374, 176, 10, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 313 [(374, 427), (176, 170), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 313 = [256, 160, 10, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 313 = [256, 160, 10, 1] by decide]; decide)

theorem bound313 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 313))
      (frozenWangTable.lower 313) := by
  have h := QiushiMatmul.plane426GenBound0044
  change QuotientRankAtLeast (spanCodes [272, 176, 102, 10, 1]) 16 at h
  have htarget := bind_contained [374, 176, 10, 1] [272, 176, 102, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 313 orbit313 htarget (by decide)

theorem orbit335 :
    frozenWangTable.OrbitImage 335 (spanCodes [282, 144, 78, 32]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 335 [(282, 98), (144, 1), (78, 199), (32, 16)]
    (codeMat 86) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 335 = [164, 98, 16, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 335 = [164, 98, 16, 1] by decide]; decide)

theorem bound335 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 335))
      (frozenWangTable.lower 335) := by
  have h := QiushiMatmul.plane486GenBound0106
  change QuotientRankAtLeast (spanCodes [272, 144, 68, 32, 10]) 16 at h
  have htarget := bind_contained [282, 144, 78, 32] [272, 144, 68, 32, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 335 orbit335 htarget (by decide)

theorem orbit381 :
    frozenWangTable.OrbitImage 381 (spanCodes [294, 133, 97, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 381 [(294, 338), (133, 261), (97, 19), (10, 344)]
    (codeMat 85) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 381 = [261, 68, 19, 10] by decide]; decide)
    (by rw [show frozenWangTable.basis 381 = [261, 68, 19, 10] by decide]; decide)

theorem bound381 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 381))
      (frozenWangTable.lower 381) := by
  have h := QiushiMatmul.step109_orbit216_lb16_wc
  change QuotientRankAtLeast (spanCodes [294, 132, 96, 10, 1]) 16 at h
  have htarget := bind_contained [294, 133, 97, 10] [294, 132, 96, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 381 orbit381 htarget (by decide)

theorem orbit436 :
    frozenWangTable.OrbitImage 436 (spanCodes [128, 96, 10]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 436 [(128, 1), (96, 20), (10, 96)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 436 = [96, 20, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 436 = [96, 20, 1] by decide]; decide)

theorem bound436 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 436))
      (frozenWangTable.lower 436) := by
  have h := QiushiMatmul.plane488GenBound0107
  change QuotientRankAtLeast (spanCodes [274, 128, 96, 10]) 17 at h
  have htarget := bind_contained [128, 96, 10] [274, 128, 96, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 436 orbit436 htarget (by decide)

theorem orbit438 :
    frozenWangTable.OrbitImage 438 (spanCodes [280, 128, 106]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 438 [(280, 21), (128, 1), (106, 115)]
    (codeMat 84) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 438 = [102, 20, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 438 = [102, 20, 1] by decide]; decide)

theorem bound438 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 438))
      (frozenWangTable.lower 438) := by
  have h := QiushiMatmul.plane488GenBound0107
  change QuotientRankAtLeast (spanCodes [274, 128, 96, 10]) 17 at h
  have htarget := bind_contained [280, 128, 106] [274, 128, 96, 10]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 438 orbit438 htarget (by decide)

end QiushiMatmul.FrozenRegistry.Transport

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``QiushiMatmul.FrozenRegistry.Transport.bound090, ``QiushiMatmul.FrozenRegistry.Transport.bound091, ``QiushiMatmul.FrozenRegistry.Transport.bound122, ``QiushiMatmul.FrozenRegistry.Transport.bound136, ``QiushiMatmul.FrozenRegistry.Transport.bound139, ``QiushiMatmul.FrozenRegistry.Transport.bound154, ``QiushiMatmul.FrozenRegistry.Transport.bound170, ``QiushiMatmul.FrozenRegistry.Transport.bound172, ``QiushiMatmul.FrozenRegistry.Transport.bound173, ``QiushiMatmul.FrozenRegistry.Transport.bound200, ``QiushiMatmul.FrozenRegistry.Transport.bound205, ``QiushiMatmul.FrozenRegistry.Transport.bound222, ``QiushiMatmul.FrozenRegistry.Transport.bound226, ``QiushiMatmul.FrozenRegistry.Transport.bound230, ``QiushiMatmul.FrozenRegistry.Transport.bound271, ``QiushiMatmul.FrozenRegistry.Transport.bound277, ``QiushiMatmul.FrozenRegistry.Transport.bound313, ``QiushiMatmul.FrozenRegistry.Transport.bound335, ``QiushiMatmul.FrozenRegistry.Transport.bound381, ``QiushiMatmul.FrozenRegistry.Transport.bound436, ``QiushiMatmul.FrozenRegistry.Transport.bound438] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"TRANSPORT_AXIOMS {name}: {axioms}"
  Lean.logInfo "TRANSPORT_CHECKED 21"
