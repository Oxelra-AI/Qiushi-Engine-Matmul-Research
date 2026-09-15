import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0332Refs : Fin 43 → RowRef 1665 43 := ![.occ 86, .occ 121, .occ 122, .occ 123, .occ 130, .occ 138, .occ 139, .occ 142, .occ 224, .occ 289, .occ 290, .occ 489, .occ 581, .occ 827, .occ 837, .occ 855, .occ 1140, .occ 1143, .occ 1150, .occ 1154, .occ 1174, .occ 1214, .occ 1215, .occ 1398, .occ 1478, .occ 1504, .occ 1558, .occ 1573, .occ 1600, .occ 1605, .occ 1608, .sumGe, .nonneg 20, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchLe 27 (0), .branchGe 37 (1)]

def plane484GenLeaf0332Mult : Fin 43 → Nat := ![808, 176, 291, 63, 76, 90, 677, 283, 31, 117, 62, 480, 101, 866, 404, 289, 551, 138, 271, 172, 271, 208, 107, 387, 34, 123, 193, 15, 70, 267, 473, 1231, 277, 757, 194, 1126, 3322, 1155, 1628, 3245, 1093, 1231, 2337]

theorem plane484GenLeaf0332 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0332Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0332Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0332Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0332Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 224
  · exact hroot.hOcc 289
  · exact hroot.hOcc 290
  · exact hroot.hOcc 489
  · exact hroot.hOcc 581
  · exact hroot.hOcc 827
  · exact hroot.hOcc 837
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1605
  · exact hroot.hOcc 1608
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
