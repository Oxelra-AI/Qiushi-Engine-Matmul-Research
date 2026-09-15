import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0097Refs : Fin 50 → RowRef 726 49 := ![.occ 96, .occ 98, .occ 112, .occ 118, .occ 171, .occ 198, .occ 219, .occ 230, .occ 231, .occ 241, .occ 244, .occ 257, .occ 258, .occ 267, .occ 275, .occ 318, .occ 319, .occ 329, .occ 332, .occ 334, .occ 350, .occ 363, .occ 365, .occ 382, .occ 394, .occ 400, .occ 402, .occ 431, .occ 436, .occ 544, .occ 547, .occ 564, .occ 565, .occ 580, .occ 585, .occ 598, .occ 605, .occ 640, .occ 662, .occ 671, .occ 709, .occ 716, .occ 722, .sumGe, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchLe 28 (0), .branchLe 0 (0)]

def plane491GenLeaf0097Mult : Fin 50 → Nat := ![140423, 800003, 852370, 885182, 33231, 897110, 203771, 272164, 72141, 127694, 51983, 402696, 205098, 27671, 220240, 57314, 248541, 547516, 199728, 601812, 326005, 440318, 268921, 391057, 81637, 101694, 310148, 350235, 105186, 56684, 4531, 366261, 1394, 57314, 273074, 9939, 18992, 235551, 512825, 432126, 38322, 142171, 600665, 1878247, 4041397, 2834422, 1642696, 1424680, 1878247, 1054819]

theorem plane491GenLeaf0097 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0097Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0097Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 171
  · exact hroot.hOcc 198
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 267
  · exact hroot.hOcc 275
  · exact hroot.hOcc 318
  · exact hroot.hOcc 319
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 363
  · exact hroot.hOcc 365
  · exact hroot.hOcc 382
  · exact hroot.hOcc 394
  · exact hroot.hOcc 400
  · exact hroot.hOcc 402
  · exact hroot.hOcc 431
  · exact hroot.hOcc 436
  · exact hroot.hOcc 544
  · exact hroot.hOcc 547
  · exact hroot.hOcc 564
  · exact hroot.hOcc 565
  · exact hroot.hOcc 580
  · exact hroot.hOcc 585
  · exact hroot.hOcc 598
  · exact hroot.hOcc 605
  · exact hroot.hOcc 640
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 709
  · exact hroot.hOcc 716
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
