import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0009Refs : Fin 26 → RowRef 74 28 := ![.occ 3, .occ 6, .occ 7, .occ 12, .occ 20, .occ 32, .occ 34, .occ 35, .occ 37, .occ 41, .occ 47, .occ 52, .occ 53, .occ 59, .occ 60, .occ 67, .occ 72, .sumGe, .nonneg 3, .nonneg 6, .nonneg 19, .nonneg 20, .branchLe 5 (0), .branchGe 2 (1), .branchLe 10 (0), .branchGe 7 (2)]

def plane315GenLeaf0009Mult : Fin 26 → Nat := ![5, 20, 9, 11, 3, 3, 7, 3, 3, 4, 11, 4, 11, 4, 3, 9, 5, 20, 5, 5, 2, 2, 3, 17, 5, 14]

theorem plane315GenLeaf0009 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (2 : Int) ≤ x 7)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0009Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0009Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 20
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (10 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
