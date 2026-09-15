import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0522Refs : Fin 44 → RowRef 1665 43 := ![.occ 129, .occ 135, .occ 138, .occ 186, .occ 296, .occ 380, .occ 381, .occ 420, .occ 532, .occ 597, .occ 675, .occ 676, .occ 677, .occ 713, .occ 732, .occ 1160, .occ 1206, .occ 1242, .occ 1340, .occ 1358, .occ 1386, .occ 1398, .occ 1402, .occ 1412, .occ 1426, .occ 1481, .occ 1540, .occ 1610, .occ 1622, .occ 1663, .sumGe, .nonneg 2, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchGe 18 (1), .branchLe 1 (0), .branchLe 12 (0), .branchLe 23 (0), .branchLe 36 (0)]

def plane484GenLeaf0522Mult : Fin 44 → Nat := ![51, 134, 344, 179, 435, 203, 83, 66, 285, 271, 50, 135, 46, 92, 71, 284, 19, 4, 214, 8, 60, 9, 102, 26, 35, 10, 114, 5, 62, 48, 458, 30, 1504, 1356, 48, 39, 174, 1814, 458, 880, 439, 410, 5, 458]

theorem plane484GenLeaf0522 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0522Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0522Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0522Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0522Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 186
  · exact hroot.hOcc 296
  · exact hroot.hOcc 380
  · exact hroot.hOcc 381
  · exact hroot.hOcc 420
  · exact hroot.hOcc 532
  · exact hroot.hOcc 597
  · exact hroot.hOcc 675
  · exact hroot.hOcc 676
  · exact hroot.hOcc 677
  · exact hroot.hOcc 713
  · exact hroot.hOcc 732
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
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
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
