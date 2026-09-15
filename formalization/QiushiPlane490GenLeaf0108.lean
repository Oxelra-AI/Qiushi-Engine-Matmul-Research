import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0108Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 95, .occ 103, .occ 106, .occ 108, .occ 112, .occ 136, .occ 141, .occ 143, .occ 146, .occ 159, .occ 160, .occ 237, .occ 248, .occ 252, .occ 279, .occ 283, .occ 291, .occ 314, .occ 326, .occ 335, .occ 360, .occ 447, .occ 484, .occ 550, .occ 562, .occ 617, .occ 632, .occ 636, .occ 649, .occ 651, .occ 683, .occ 696, .occ 697, .occ 709, .sumGe, .nonneg 14, .nonneg 35, .branchGe 29 (1), .branchGe 18 (1), .branchGe 1 (1), .branchGe 20 (1), .branchGe 8 (1), .branchLe 0 (0)]

def plane490GenLeaf0108Mult : Fin 44 → Nat := ![39, 1836, 227, 3044, 1664, 108, 1850, 275, 528, 1373, 625, 2346, 399, 346, 328, 309, 674, 425, 858, 227, 322, 479, 463, 737, 549, 619, 721, 581, 606, 793, 1529, 344, 205, 794, 463, 3249, 357, 90, 7901, 5855, 2226, 8864, 7237, 3249]

theorem plane490GenLeaf0108 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0108Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0108Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 237
  · exact hroot.hOcc 248
  · exact hroot.hOcc 252
  · exact hroot.hOcc 279
  · exact hroot.hOcc 283
  · exact hroot.hOcc 291
  · exact hroot.hOcc 314
  · exact hroot.hOcc 326
  · exact hroot.hOcc 335
  · exact hroot.hOcc 360
  · exact hroot.hOcc 447
  · exact hroot.hOcc 484
  · exact hroot.hOcc 550
  · exact hroot.hOcc 562
  · exact hroot.hOcc 617
  · exact hroot.hOcc 632
  · exact hroot.hOcc 636
  · exact hroot.hOcc 649
  · exact hroot.hOcc 651
  · exact hroot.hOcc 683
  · exact hroot.hOcc 696
  · exact hroot.hOcc 697
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
