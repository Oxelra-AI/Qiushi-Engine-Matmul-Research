import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0004Refs : Fin 14 → RowRef 74 28 := ![.occ 24, .occ 27, .occ 35, .occ 36, .occ 37, .occ 47, .occ 53, .occ 58, .sumGe, .nonneg 3, .nonneg 17, .nonneg 20, .branchGe 4 (2), .branchGe 21 (1)]

def plane315GenLeaf0004Mult : Fin 14 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5]

theorem plane315GenLeaf0004 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_4 : (2 : Int) ≤ x 4)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0004Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0004Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 47
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (4 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (21 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
