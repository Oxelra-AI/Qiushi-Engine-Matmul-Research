import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0498Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 126, .occ 129, .occ 131, .occ 135, .occ 138, .occ 141, .occ 142, .occ 186, .occ 279, .occ 367, .occ 439, .occ 581, .occ 595, .occ 634, .occ 783, .occ 916, .occ 951, .occ 1087, .occ 1159, .occ 1206, .occ 1248, .occ 1446, .occ 1467, .occ 1511, .occ 1512, .occ 1530, .occ 1535, .occ 1548, .occ 1642, .occ 1645, .occ 1653, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchGe 36 (1), .branchGe 28 (1), .branchLe 38 (0)]

def plane484GenLeaf0498Mult : Fin 42 → Nat := ![47, 53, 78, 1, 101, 7, 60, 6, 23, 48, 17, 35, 35, 15, 11, 61, 82, 10, 34, 15, 50, 69, 35, 69, 77, 20, 5, 23, 68, 15, 33, 50, 14, 228, 629, 109, 470, 228, 110, 361, 257, 228]

theorem plane484GenLeaf0498 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0498Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0498Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0498Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0498Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 186
  · exact hroot.hOcc 279
  · exact hroot.hOcc 367
  · exact hroot.hOcc 439
  · exact hroot.hOcc 581
  · exact hroot.hOcc 595
  · exact hroot.hOcc 634
  · exact hroot.hOcc 783
  · exact hroot.hOcc 916
  · exact hroot.hOcc 951
  · exact hroot.hOcc 1087
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
