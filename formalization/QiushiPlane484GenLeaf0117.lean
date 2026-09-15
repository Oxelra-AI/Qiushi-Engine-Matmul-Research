import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0117Refs : Fin 43 → RowRef 1665 43 := ![.occ 125, .occ 137, .occ 139, .occ 141, .occ 142, .occ 179, .occ 289, .occ 346, .occ 354, .occ 359, .occ 615, .occ 705, .occ 965, .occ 992, .occ 1079, .occ 1088, .occ 1238, .occ 1264, .occ 1298, .occ 1325, .occ 1346, .occ 1384, .occ 1399, .occ 1422, .occ 1438, .occ 1451, .occ 1477, .occ 1503, .occ 1504, .occ 1573, .occ 1620, .sumGe, .nonneg 0, .nonneg 19, .nonneg 24, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchGe 21 (1), .branchGe 18 (1)]

def plane484GenLeaf0117Mult : Fin 43 → Nat := ![351, 342, 2110, 1414, 724, 725, 121, 234, 3068, 1783, 341, 275, 411, 744, 825, 602, 148, 438, 107, 85, 1084, 184, 622, 462, 108, 1459, 341, 323, 846, 723, 931, 3176, 234, 3464, 3513, 2345, 1639, 3176, 7488, 6962, 5635, 4961, 14664]

theorem plane484GenLeaf0117 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0117Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0117Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0117Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0117Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 179
  · exact hroot.hOcc 289
  · exact hroot.hOcc 346
  · exact hroot.hOcc 354
  · exact hroot.hOcc 359
  · exact hroot.hOcc 615
  · exact hroot.hOcc 705
  · exact hroot.hOcc 965
  · exact hroot.hOcc 992
  · exact hroot.hOcc 1079
  · exact hroot.hOcc 1088
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1620
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
