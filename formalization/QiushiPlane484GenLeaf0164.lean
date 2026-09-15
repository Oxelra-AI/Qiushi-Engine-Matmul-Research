import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0164Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 126, .occ 127, .occ 129, .occ 173, .occ 181, .occ 462, .occ 542, .occ 632, .occ 672, .occ 745, .occ 818, .occ 975, .occ 1164, .occ 1215, .occ 1230, .occ 1232, .occ 1239, .occ 1262, .occ 1271, .occ 1315, .occ 1353, .occ 1379, .occ 1405, .occ 1455, .occ 1509, .occ 1512, .occ 1557, .occ 1622, .occ 1647, .sumGe, .nonneg 3, .nonneg 6, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchLe 33 (0), .branchLe 0 (0), .branchGe 14 (1)]

def plane484GenLeaf0164Mult : Fin 44 → Nat := ![3, 631, 793, 161, 208, 108, 169, 167, 45, 363, 346, 124, 223, 211, 139, 75, 166, 88, 49, 228, 48, 51, 259, 279, 48, 116, 111, 88, 237, 60, 932, 136, 1684, 467, 238, 1236, 932, 2450, 844, 1112, 741, 766, 272, 3522]

theorem plane484GenLeaf0164 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0164Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0164Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0164Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0164Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 173
  · exact hroot.hOcc 181
  · exact hroot.hOcc 462
  · exact hroot.hOcc 542
  · exact hroot.hOcc 632
  · exact hroot.hOcc 672
  · exact hroot.hOcc 745
  · exact hroot.hOcc 818
  · exact hroot.hOcc 975
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
