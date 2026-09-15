import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0007Refs : Fin 22 → RowRef 74 28 := ![.occ 6, .occ 7, .occ 9, .occ 12, .occ 15, .occ 23, .occ 26, .occ 34, .occ 37, .occ 40, .occ 41, .occ 47, .occ 51, .occ 53, .occ 63, .occ 67, .sumGe, .nonneg 6, .branchLe 5 (0), .branchGe 2 (1), .branchLe 10 (0), .branchGe 3 (1)]

def plane315GenLeaf0007Mult : Fin 22 → Nat := ![6, 4, 3, 2, 2, 1, 3, 4, 2, 1, 2, 3, 3, 1, 3, 1, 6, 2, 5, 5, 2, 11]

theorem plane315GenLeaf0007 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0007Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0007Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (10 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
