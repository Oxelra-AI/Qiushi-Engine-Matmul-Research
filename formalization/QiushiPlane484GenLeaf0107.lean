import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0107Refs : Fin 40 → RowRef 1665 43 := ![.occ 119, .occ 130, .occ 134, .occ 135, .occ 179, .occ 198, .occ 204, .occ 211, .occ 357, .occ 421, .occ 423, .occ 653, .occ 793, .occ 919, .occ 921, .occ 1143, .occ 1341, .occ 1347, .occ 1385, .occ 1387, .occ 1446, .occ 1449, .occ 1455, .occ 1477, .occ 1537, .occ 1618, .occ 1638, .occ 1661, .sumGe, .nonneg 18, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchLe 19 (0), .branchLe 34 (0), .branchGe 25 (1), .branchGe 20 (1)]

def plane484GenLeaf0107Mult : Fin 40 → Nat := ![86, 65, 90, 104, 65, 81, 78, 12, 86, 24, 24, 125, 25, 12, 33, 65, 4, 39, 23, 12, 23, 19, 18, 49, 116, 30, 12, 23, 204, 43, 42, 23, 200, 728, 395, 54, 162, 90, 331, 545]

theorem plane484GenLeaf0107 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0107Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0107Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 179
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 211
  · exact hroot.hOcc 357
  · exact hroot.hOcc 421
  · exact hroot.hOcc 423
  · exact hroot.hOcc 653
  · exact hroot.hOcc 793
  · exact hroot.hOcc 919
  · exact hroot.hOcc 921
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
