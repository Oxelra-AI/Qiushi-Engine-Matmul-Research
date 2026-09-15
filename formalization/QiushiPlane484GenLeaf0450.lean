import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0450Refs : Fin 37 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 128, .occ 130, .occ 131, .occ 133, .occ 138, .occ 186, .occ 641, .occ 773, .occ 892, .occ 1205, .occ 1206, .occ 1249, .occ 1252, .occ 1280, .occ 1298, .occ 1329, .occ 1331, .occ 1350, .occ 1426, .occ 1442, .occ 1552, .occ 1553, .occ 1606, .sumGe, .nonneg 0, .nonneg 1, .nonneg 19, .nonneg 20, .nonneg 21, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchGe 23 (1), .branchGe 10 (1)]

def plane484GenLeaf0450Mult : Fin 37 → Nat := ![105, 27, 103, 37, 138, 54, 236, 126, 34, 168, 12, 102, 4, 90, 40, 16, 20, 60, 28, 28, 20, 10, 48, 28, 38, 236, 82, 54, 220, 60, 20, 638, 56, 236, 236, 590, 852]

theorem plane484GenLeaf0450 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0450Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0450Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0450Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0450Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 186
  · exact hroot.hOcc 641
  · exact hroot.hOcc 773
  · exact hroot.hOcc 892
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
