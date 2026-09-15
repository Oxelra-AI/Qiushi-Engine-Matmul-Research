import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0184Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 131, .occ 141, .occ 143, .occ 212, .occ 214, .occ 216, .occ 220, .occ 242, .occ 437, .occ 682, .occ 781, .occ 979, .occ 1183, .occ 1214, .occ 1236, .occ 1326, .occ 1357, .occ 1445, .occ 1488, .occ 1505, .occ 1557, .occ 1561, .occ 1571, .occ 1606, .occ 1607, .occ 1619, .occ 1623, .occ 1634, .occ 1652, .occ 1664, .sumGe, .nonneg 27, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 7 (1), .branchLe 39 (0), .branchLe 22 (0), .branchGe 19 (1)]

def plane484GenLeaf0184Mult : Fin 44 → Nat := ![516, 82, 331, 345, 398, 829, 117, 698, 113, 922, 156, 571, 134, 251, 270, 740, 781, 81, 58, 312, 2, 233, 148, 429, 81, 296, 76, 1, 146, 74, 19, 1483, 526, 1232, 4320, 4110, 286, 860, 1139, 1482, 3358, 1483, 1054, 3031]

theorem plane484GenLeaf0184 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0184Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0184Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0184Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0184Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 131
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 212
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 242
  · exact hroot.hOcc 437
  · exact hroot.hOcc 682
  · exact hroot.hOcc 781
  · exact hroot.hOcc 979
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
