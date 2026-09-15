import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0376Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 125, .occ 133, .occ 137, .occ 388, .occ 459, .occ 469, .occ 589, .occ 615, .occ 1119, .occ 1143, .occ 1151, .occ 1173, .occ 1179, .occ 1186, .occ 1234, .occ 1304, .occ 1314, .occ 1342, .occ 1353, .occ 1357, .occ 1484, .occ 1501, .occ 1515, .occ 1516, .occ 1527, .occ 1597, .occ 1640, .occ 1652, .sumGe, .nonneg 17, .nonneg 20, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchLe 27 (0), .branchGe 21 (1)]

def plane484GenLeaf0376Mult : Fin 43 → Nat := ![9821, 3022, 5342, 11690, 22180, 9089, 1906, 2251, 134, 12538, 698, 3721, 6101, 2235, 416, 416, 2625, 400, 7729, 248, 5693, 1714, 2130, 3890, 3305, 654, 2657, 1605, 928, 2368, 22180, 38463, 928, 2007, 2007, 26078, 18460, 46149, 16504, 18231, 20050, 20575, 72356]

theorem plane484GenLeaf0376 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0376Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0376Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0376Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0376Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 388
  · exact hroot.hOcc 459
  · exact hroot.hOcc 469
  · exact hroot.hOcc 589
  · exact hroot.hOcc 615
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
