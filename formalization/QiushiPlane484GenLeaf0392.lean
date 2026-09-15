import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0392Refs : Fin 36 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 126, .occ 127, .occ 129, .occ 133, .occ 134, .occ 136, .occ 137, .occ 138, .occ 144, .occ 173, .occ 279, .occ 777, .occ 778, .occ 838, .occ 843, .occ 1144, .occ 1168, .occ 1183, .occ 1208, .occ 1409, .occ 1457, .occ 1488, .occ 1530, .sumGe, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 31 (0), .branchLe 24 (0), .branchLe 37 (0), .branchLe 35 (0), .branchLe 33 (0), .branchLe 39 (0)]

def plane484GenLeaf0392Mult : Fin 36 → Nat := ![19, 12, 14, 9, 13, 6, 2, 12, 2, 14, 7, 4, 8, 16, 4, 4, 12, 8, 8, 12, 8, 4, 8, 8, 8, 40, 6, 16, 42, 114, 28, 28, 40, 24, 40, 40]

theorem plane484GenLeaf0392 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0392Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0392Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0392Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0392Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 173
  · exact hroot.hOcc 279
  · exact hroot.hOcc 777
  · exact hroot.hOcc 778
  · exact hroot.hOcc 838
  · exact hroot.hOcc 843
  · exact hroot.hOcc 1144
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1530
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
