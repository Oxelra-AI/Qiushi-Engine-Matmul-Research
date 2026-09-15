import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0436Refs : Fin 37 → RowRef 1665 43 := ![.occ 105, .occ 119, .occ 120, .occ 122, .occ 133, .occ 138, .occ 143, .occ 163, .occ 166, .occ 180, .occ 531, .occ 573, .occ 610, .occ 738, .occ 762, .occ 1044, .occ 1066, .occ 1191, .occ 1200, .occ 1327, .occ 1348, .occ 1353, .occ 1458, .occ 1580, .sumGe, .nonneg 1, .nonneg 2, .nonneg 23, .branchGe 15 (1), .branchLe 35 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchLe 20 (0), .branchLe 38 (0), .branchGe 11 (1)]

def plane484GenLeaf0436Mult : Fin 37 → Nat := ![4, 7, 1, 1, 12, 12, 6, 4, 6, 5, 12, 6, 8, 6, 2, 4, 4, 1, 1, 1, 3, 1, 1, 1, 13, 2, 12, 12, 32, 9, 4, 12, 35, 12, 13, 13, 54]

theorem plane484GenLeaf0436 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0436Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0436Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0436Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0436Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 180
  · exact hroot.hOcc 531
  · exact hroot.hOcc 573
  · exact hroot.hOcc 610
  · exact hroot.hOcc 738
  · exact hroot.hOcc 762
  · exact hroot.hOcc 1044
  · exact hroot.hOcc 1066
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1580
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
