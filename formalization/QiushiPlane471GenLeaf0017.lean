import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0017Refs : Fin 30 → RowRef 304 63 := ![.occ 1, .occ 4, .occ 14, .occ 15, .occ 63, .occ 68, .occ 77, .occ 78, .occ 108, .occ 109, .occ 123, .occ 124, .occ 127, .occ 157, .occ 160, .occ 166, .occ 288, .occ 292, .occ 294, .occ 299, .sumGe, .nonneg 21, .nonneg 30, .nonneg 35, .nonneg 44, .nonneg 48, .nonneg 49, .nonneg 55, .nonneg 58, .branchGe 8 (1)]

def plane471GenLeaf0017Mult : Fin 30 → Nat := ![2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 6, 2, 2, 2, 2, 1, 3, 3, 1, 6, 4, 4, 4, 4, 8, 12, 8, 12, 44]

theorem plane471GenLeaf0017 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_48 : x 48 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0017Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0017Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 4
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 166
  · exact hroot.hOcc 288
  · exact hroot.hOcc 292
  · exact hroot.hOcc 294
  · exact hroot.hOcc 299
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (35 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (8 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
