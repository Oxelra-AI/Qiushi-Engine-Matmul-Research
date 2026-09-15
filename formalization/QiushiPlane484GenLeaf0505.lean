import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0505Refs : Fin 34 → RowRef 1665 43 := ![.occ 129, .occ 133, .occ 140, .occ 143, .occ 173, .occ 336, .occ 441, .occ 443, .occ 507, .occ 624, .occ 778, .occ 806, .occ 995, .occ 1112, .occ 1162, .occ 1174, .occ 1195, .occ 1235, .occ 1296, .occ 1377, .occ 1410, .occ 1509, .occ 1510, .occ 1531, .occ 1590, .sumGe, .nonneg 1, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 32 (1), .branchGe 39 (1), .branchGe 17 (1)]

def plane484GenLeaf0505Mult : Fin 34 → Nat := ![7, 18, 6, 7, 1, 9, 1, 18, 1, 15, 3, 6, 17, 4, 19, 6, 19, 2, 7, 14, 3, 1, 8, 1, 16, 26, 24, 15, 43, 12, 129, 86, 108, 114]

theorem plane484GenLeaf0505 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0505Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0505Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0505Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0505Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 173
  · exact hroot.hOcc 336
  · exact hroot.hOcc 441
  · exact hroot.hOcc 443
  · exact hroot.hOcc 507
  · exact hroot.hOcc 624
  · exact hroot.hOcc 778
  · exact hroot.hOcc 806
  · exact hroot.hOcc 995
  · exact hroot.hOcc 1112
  · exact hroot.hOcc 1162
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1195
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1590
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
