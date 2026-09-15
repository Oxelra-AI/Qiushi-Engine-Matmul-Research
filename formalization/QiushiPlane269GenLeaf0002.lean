import QiushiPlane269GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane269GenLeaf0002Refs : Fin 16 → RowRef 30 21 := ![.occ 12, .occ 13, .occ 14, .occ 16, .occ 21, .occ 23, .occ 24, .occ 27, .occ 28, .occ 29, .sumGe, .nonneg 4, .nonneg 6, .nonneg 7, .nonneg 8, .branchGe 1 (2)]

def plane269GenLeaf0002Mult : Fin 16 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2]

theorem plane269GenLeaf0002 (x : Fin 21 → Int)
    (hroot : plane269GenOccSys.RootHolds x)
    (hLB_1 : (2 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane269GenLeaf0002Refs i).resolveCoeff plane269GenOccSys j)
    (fun i => (plane269GenLeaf0002Refs i).resolveRhs plane269GenOccSys) plane269GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane269GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane269GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 21) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (6 : Fin 21) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (7 : Fin 21) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 21) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (1 : Fin 21) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
