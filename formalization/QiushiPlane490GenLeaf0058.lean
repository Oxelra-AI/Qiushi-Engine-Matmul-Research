import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0058Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 90, .occ 112, .occ 113, .occ 121, .occ 135, .occ 143, .occ 191, .occ 211, .occ 219, .occ 233, .occ 247, .occ 284, .occ 291, .occ 293, .occ 302, .occ 336, .occ 362, .occ 367, .occ 370, .occ 379, .occ 421, .occ 438, .occ 461, .occ 583, .occ 601, .occ 610, .occ 617, .occ 619, .occ 632, .occ 649, .occ 668, .occ 678, .occ 702, .sumGe, .nonneg 27, .nonneg 37, .nonneg 38, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchGe 6 (1), .branchGe 22 (1)]

def plane490GenLeaf0058Mult : Fin 44 → Nat := ![2368, 900, 239, 2290, 266, 266, 162, 2543, 615, 1067, 43, 3451, 847, 314, 670, 253, 1657, 1221, 195, 574, 401, 670, 158, 1793, 68, 334, 602, 653, 215, 653, 1005, 82, 216, 908, 3451, 1793, 1482, 224, 2798, 3137, 7580, 10826, 3257, 8580]

theorem plane490GenLeaf0058 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0058Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0058Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0058Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0058Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 90
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 135
  · exact hroot.hOcc 143
  · exact hroot.hOcc 191
  · exact hroot.hOcc 211
  · exact hroot.hOcc 219
  · exact hroot.hOcc 233
  · exact hroot.hOcc 247
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 293
  · exact hroot.hOcc 302
  · exact hroot.hOcc 336
  · exact hroot.hOcc 362
  · exact hroot.hOcc 367
  · exact hroot.hOcc 370
  · exact hroot.hOcc 379
  · exact hroot.hOcc 421
  · exact hroot.hOcc 438
  · exact hroot.hOcc 461
  · exact hroot.hOcc 583
  · exact hroot.hOcc 601
  · exact hroot.hOcc 610
  · exact hroot.hOcc 617
  · exact hroot.hOcc 619
  · exact hroot.hOcc 632
  · exact hroot.hOcc 649
  · exact hroot.hOcc 668
  · exact hroot.hOcc 678
  · exact hroot.hOcc 702
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
