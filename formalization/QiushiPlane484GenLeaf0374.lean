import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0374Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 126, .occ 131, .occ 132, .occ 137, .occ 138, .occ 203, .occ 223, .occ 227, .occ 237, .occ 287, .occ 288, .occ 390, .occ 455, .occ 907, .occ 1143, .occ 1147, .occ 1159, .occ 1160, .occ 1173, .occ 1179, .occ 1206, .occ 1213, .occ 1216, .occ 1314, .occ 1320, .occ 1322, .occ 1567, .occ 1573, .occ 1649, .occ 1657, .sumGe, .nonneg 15, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchLe 27 (0), .branchLe 21 (0), .branchLe 9 (0), .branchGe 34 (1)]

def plane484GenLeaf0374Mult : Fin 44 → Nat := ![17, 737, 432, 713, 441, 206, 989, 182, 272, 41, 48, 285, 147, 240, 585, 468, 548, 5, 387, 68, 68, 677, 556, 271, 8, 56, 6, 177, 198, 494, 124, 74, 1702, 943, 1907, 1196, 3751, 2127, 1072, 1702, 1697, 754, 683, 2414]

theorem plane484GenLeaf0374 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0374Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0374Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0374Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0374Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 203
  · exact hroot.hOcc 223
  · exact hroot.hOcc 227
  · exact hroot.hOcc 237
  · exact hroot.hOcc 287
  · exact hroot.hOcc 288
  · exact hroot.hOcc 390
  · exact hroot.hOcc 455
  · exact hroot.hOcc 907
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
