import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0013Refs : Fin 29 → RowRef 74 28 := ![.occ 5, .occ 7, .occ 8, .occ 10, .occ 12, .occ 13, .occ 22, .occ 26, .occ 28, .occ 34, .occ 35, .occ 37, .occ 39, .occ 47, .occ 49, .occ 53, .occ 54, .occ 56, .occ 58, .occ 59, .occ 62, .occ 67, .occ 69, .occ 70, .sumGe, .nonneg 17, .nonneg 19, .branchGe 5 (1), .branchGe 1 (1)]

def plane315GenLeaf0013Mult : Fin 29 → Nat := ![74, 44, 6, 4, 8, 2, 4, 12, 56, 18, 26, 26, 14, 22, 5, 12, 3, 41, 5, 7, 1, 46, 2, 8, 78, 108, 108, 108, 48]

theorem plane315GenLeaf0013 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0013Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0013Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 22
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (5 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
