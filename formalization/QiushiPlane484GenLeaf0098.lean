import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0098Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 130, .occ 137, .occ 141, .occ 180, .occ 193, .occ 256, .occ 602, .occ 628, .occ 738, .occ 855, .occ 861, .occ 1001, .occ 1002, .occ 1078, .occ 1146, .occ 1172, .occ 1213, .occ 1215, .occ 1249, .occ 1250, .occ 1298, .occ 1319, .occ 1371, .occ 1379, .occ 1437, .occ 1441, .occ 1478, .occ 1530, .occ 1545, .occ 1573, .sumGe, .nonneg 1, .nonneg 2, .nonneg 10, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchGe 28 (1), .branchLe 8 (0), .branchGe 13 (1)]

def plane484GenLeaf0098Mult : Fin 44 → Nat := ![203, 214, 98, 44, 11, 7, 20, 63, 42, 27, 184, 233, 113, 11, 105, 22, 8, 33, 11, 40, 117, 60, 30, 11, 25, 49, 143, 11, 8, 30, 8, 266, 22, 76, 1022, 38, 255, 1273, 149, 419, 266, 486, 22, 1256]

theorem plane484GenLeaf0098 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0098Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0098Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 180
  · exact hroot.hOcc 193
  · exact hroot.hOcc 256
  · exact hroot.hOcc 602
  · exact hroot.hOcc 628
  · exact hroot.hOcc 738
  · exact hroot.hOcc 855
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1001
  · exact hroot.hOcc 1002
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1573
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
