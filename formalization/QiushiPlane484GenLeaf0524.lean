import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0524Refs : Fin 44 → RowRef 1665 43 := ![.occ 129, .occ 131, .occ 138, .occ 195, .occ 199, .occ 296, .occ 432, .occ 510, .occ 597, .occ 731, .occ 1078, .occ 1084, .occ 1160, .occ 1200, .occ 1299, .occ 1314, .occ 1342, .occ 1358, .occ 1380, .occ 1408, .occ 1412, .occ 1426, .occ 1454, .occ 1499, .occ 1529, .occ 1540, .occ 1609, .occ 1633, .occ 1652, .occ 1664, .sumGe, .nonneg 19, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchGe 18 (1), .branchLe 1 (0), .branchLe 12 (0), .branchGe 23 (1)]

def plane484GenLeaf0524Mult : Fin 44 → Nat := ![210, 1875, 2306, 303, 417, 3060, 1364, 670, 182, 211, 40, 27, 78, 565, 544, 51, 1255, 281, 434, 269, 5, 516, 386, 277, 823, 105, 772, 623, 1338, 278, 3494, 3031, 565, 7218, 4387, 2156, 565, 2851, 5967, 3494, 4587, 2156, 3216, 6987]

theorem plane484GenLeaf0524 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0524Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0524Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0524Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0524Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 296
  · exact hroot.hOcc 432
  · exact hroot.hOcc 510
  · exact hroot.hOcc 597
  · exact hroot.hOcc 731
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1084
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
