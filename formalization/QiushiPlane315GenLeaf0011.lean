import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0011Refs : Fin 20 → RowRef 74 28 := ![.occ 4, .occ 7, .occ 11, .occ 13, .occ 18, .occ 25, .occ 26, .occ 34, .occ 37, .occ 46, .occ 47, .occ 64, .occ 69, .occ 72, .sumGe, .nonneg 3, .nonneg 19, .branchLe 5 (0), .branchGe 10 (1), .branchGe 8 (2)]

def plane315GenLeaf0011Mult : Fin 20 → Nat := ![2, 6, 2, 4, 4, 6, 6, 4, 3, 1, 3, 1, 2, 2, 6, 6, 4, 2, 14, 6]

theorem plane315GenLeaf0011 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_8 : (2 : Int) ≤ x 8)
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0011Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0011Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 18
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (10 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
