import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0044Refs : Fin 25 → RowRef 100 28 := ![.occ 4, .occ 6, .occ 9, .occ 12, .occ 13, .occ 15, .occ 20, .occ 33, .occ 44, .occ 47, .occ 52, .occ 56, .occ 60, .occ 64, .occ 66, .occ 74, .occ 88, .occ 90, .sumGe, .nonneg 13, .nonneg 20, .nonneg 26, .branchGe 12 (1), .branchGe 8 (2), .branchGe 24 (1)]

def plane282GenLeaf0044Mult : Fin 25 → Nat := ![2, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 8]

theorem plane282GenLeaf0044 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_8 : (2 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0044Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0044Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0044Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0044Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 33
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 74
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
