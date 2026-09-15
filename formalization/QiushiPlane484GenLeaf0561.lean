import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0561Refs : Fin 42 → RowRef 1665 43 := ![.occ 133, .occ 137, .occ 140, .occ 152, .occ 290, .occ 325, .occ 366, .occ 706, .occ 795, .occ 914, .occ 959, .occ 974, .occ 1013, .occ 1158, .occ 1159, .occ 1160, .occ 1233, .occ 1254, .occ 1266, .occ 1303, .occ 1334, .occ 1341, .occ 1352, .occ 1377, .occ 1398, .occ 1440, .occ 1520, .occ 1547, .occ 1555, .occ 1561, .occ 1609, .sumGe, .nonneg 1, .nonneg 20, .nonneg 22, .nonneg 23, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 26 (1), .branchGe 17 (1), .branchGe 5 (1)]

def plane484GenLeaf0561Mult : Fin 42 → Nat := ![32, 34, 430, 62, 2, 396, 364, 22, 30, 312, 237, 90, 101, 26, 6, 30, 2, 60, 129, 79, 28, 208, 10, 61, 265, 72, 24, 268, 29, 53, 2, 430, 32, 1326, 1494, 32, 1558, 1224, 34, 2844, 1482, 554]

theorem plane484GenLeaf0561 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0561Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0561Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0561Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0561Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 152
  · exact hroot.hOcc 290
  · exact hroot.hOcc 325
  · exact hroot.hOcc 366
  · exact hroot.hOcc 706
  · exact hroot.hOcc 795
  · exact hroot.hOcc 914
  · exact hroot.hOcc 959
  · exact hroot.hOcc 974
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
