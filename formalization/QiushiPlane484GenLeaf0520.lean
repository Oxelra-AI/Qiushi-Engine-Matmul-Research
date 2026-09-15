import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0520Refs : Fin 43 → RowRef 1665 43 := ![.occ 124, .occ 129, .occ 131, .occ 163, .occ 278, .occ 296, .occ 329, .occ 460, .occ 532, .occ 675, .occ 861, .occ 968, .occ 1172, .occ 1173, .occ 1179, .occ 1191, .occ 1200, .occ 1219, .occ 1250, .occ 1378, .occ 1386, .occ 1397, .occ 1412, .occ 1449, .occ 1481, .occ 1483, .occ 1484, .occ 1536, .occ 1539, .occ 1602, .occ 1622, .occ 1652, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchLe 18 (0), .branchLe 3 (0), .branchGe 13 (1)]

def plane484GenLeaf0520Mult : Fin 43 → Nat := ![31, 4, 38, 42, 43, 27, 31, 74, 21, 3, 59, 21, 5, 30, 11, 59, 10, 24, 3, 42, 8, 5, 8, 5, 1, 20, 37, 27, 3, 32, 25, 57, 158, 278, 148, 34, 109, 118, 233, 158, 91, 158, 483]

theorem plane484GenLeaf0520 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0520Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0520Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0520Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0520Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 163
  · exact hroot.hOcc 278
  · exact hroot.hOcc 296
  · exact hroot.hOcc 329
  · exact hroot.hOcc 460
  · exact hroot.hOcc 532
  · exact hroot.hOcc 675
  · exact hroot.hOcc 861
  · exact hroot.hOcc 968
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1219
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
