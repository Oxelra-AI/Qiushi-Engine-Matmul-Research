import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0010Refs : Fin 27 → RowRef 74 28 := ![.occ 4, .occ 6, .occ 7, .occ 12, .occ 13, .occ 18, .occ 27, .occ 28, .occ 34, .occ 37, .occ 43, .occ 47, .occ 48, .occ 53, .occ 57, .occ 59, .occ 63, .occ 68, .occ 69, .occ 72, .sumGe, .nonneg 3, .nonneg 19, .branchLe 5 (0), .branchGe 2 (1), .branchGe 10 (1), .branchLe 8 (1)]

def plane315GenLeaf0010Mult : Fin 27 → Nat := ![7, 14, 21, 14, 18, 18, 12, 8, 18, 8, 3, 15, 10, 7, 7, 10, 7, 7, 3, 10, 35, 20, 3, 14, 17, 66, 25]

theorem plane315GenLeaf0010 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0010Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0010Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 18
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 43
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (10 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
