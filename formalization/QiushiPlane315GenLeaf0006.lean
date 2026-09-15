import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0006Refs : Fin 27 → RowRef 74 28 := ![.occ 4, .occ 6, .occ 7, .occ 12, .occ 26, .occ 32, .occ 37, .occ 39, .occ 40, .occ 47, .occ 50, .occ 51, .occ 53, .occ 58, .occ 59, .occ 67, .occ 72, .sumGe, .nonneg 5, .nonneg 19, .nonneg 24, .branchGe 2 (1), .branchLe 10 (0), .branchLe 7 (1), .branchLe 6 (0), .branchLe 3 (0), .branchGe 8 (2)]

def plane315GenLeaf0006Mult : Fin 27 → Nat := ![7, 35, 25, 10, 13, 8, 5, 4, 3, 17, 10, 2, 14, 8, 4, 18, 12, 35, 5, 16, 5, 11, 23, 3, 3, 13, 26]

theorem plane315GenLeaf0006 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_8 : (2 : Int) ≤ x 8)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0006Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0006Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 26
  · exact hroot.hOcc 32
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (10 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (6 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (3 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
