import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0103Refs : Fin 44 → RowRef 713 43 := ![.occ 94, .occ 103, .occ 105, .occ 108, .occ 109, .occ 124, .occ 144, .occ 159, .occ 164, .occ 188, .occ 197, .occ 198, .occ 250, .occ 291, .occ 299, .occ 330, .occ 336, .occ 340, .occ 354, .occ 406, .occ 480, .occ 501, .occ 506, .occ 507, .occ 509, .occ 517, .occ 521, .occ 586, .occ 602, .occ 608, .occ 675, .occ 680, .occ 683, .occ 710, .occ 712, .sumGe, .nonneg 10, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 20 (0), .branchLe 15 (0), .branchGe 12 (1)]

def plane490GenLeaf0103Mult : Fin 44 → Nat := ![8, 1684, 4872, 3054, 4044, 3712, 1882, 5100, 8, 386, 1858, 4330, 572, 1534, 2078, 138, 1452, 1568, 3558, 470, 1112, 560, 224, 1730, 552, 1180, 1336, 224, 890, 2562, 432, 203, 2079, 1115, 349, 7524, 1112, 19998, 6566, 4892, 5338, 7524, 5522, 23526]

theorem plane490GenLeaf0103 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0103Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0103Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 124
  · exact hroot.hOcc 144
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 188
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · exact hroot.hOcc 250
  · exact hroot.hOcc 291
  · exact hroot.hOcc 299
  · exact hroot.hOcc 330
  · exact hroot.hOcc 336
  · exact hroot.hOcc 340
  · exact hroot.hOcc 354
  · exact hroot.hOcc 406
  · exact hroot.hOcc 480
  · exact hroot.hOcc 501
  · exact hroot.hOcc 506
  · exact hroot.hOcc 507
  · exact hroot.hOcc 509
  · exact hroot.hOcc 517
  · exact hroot.hOcc 521
  · exact hroot.hOcc 586
  · exact hroot.hOcc 602
  · exact hroot.hOcc 608
  · exact hroot.hOcc 675
  · exact hroot.hOcc 680
  · exact hroot.hOcc 683
  · exact hroot.hOcc 710
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
