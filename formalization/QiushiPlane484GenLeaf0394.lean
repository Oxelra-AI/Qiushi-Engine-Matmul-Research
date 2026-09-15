import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0394Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 126, .occ 134, .occ 136, .occ 137, .occ 141, .occ 504, .occ 507, .occ 620, .occ 622, .occ 750, .occ 777, .occ 778, .occ 838, .occ 843, .occ 1170, .occ 1183, .occ 1188, .occ 1191, .occ 1208, .occ 1270, .occ 1282, .occ 1353, .occ 1452, .occ 1455, .occ 1458, .occ 1459, .occ 1488, .occ 1530, .occ 1658, .sumGe, .nonneg 3, .nonneg 8, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchLe 37 (0), .branchLe 35 (0), .branchLe 33 (0), .branchGe 11 (1)]

def plane484GenLeaf0394Mult : Fin 44 → Nat := ![2345, 2745, 3313, 170, 758, 2322, 85, 192, 666, 631, 1413, 955, 153, 676, 760, 279, 993, 445, 787, 85, 138, 561, 342, 677, 1470, 285, 66, 410, 85, 223, 571, 4100, 4874, 85, 2742, 3695, 8406, 445, 2868, 3342, 2357, 2884, 4034, 13464]

theorem plane484GenLeaf0394 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0394Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0394Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0394Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0394Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 504
  · exact hroot.hOcc 507
  · exact hroot.hOcc 620
  · exact hroot.hOcc 622
  · exact hroot.hOcc 750
  · exact hroot.hOcc 777
  · exact hroot.hOcc 778
  · exact hroot.hOcc 838
  · exact hroot.hOcc 843
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
