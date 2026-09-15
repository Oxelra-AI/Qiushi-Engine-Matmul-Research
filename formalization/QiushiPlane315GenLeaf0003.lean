import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0003Refs : Fin 24 → RowRef 74 28 := ![.occ 5, .occ 13, .occ 15, .occ 21, .occ 33, .occ 41, .occ 43, .occ 46, .occ 48, .occ 53, .occ 57, .occ 58, .occ 63, .occ 65, .occ 71, .occ 72, .sumGe, .nonneg 17, .nonneg 22, .branchLe 5 (0), .branchLe 2 (0), .branchGe 12 (1), .branchGe 4 (2), .branchLe 21 (0)]

def plane315GenLeaf0003Mult : Fin 24 → Nat := ![10, 2, 8, 4, 6, 6, 2, 1, 1, 5, 1, 4, 5, 3, 2, 6, 12, 6, 2, 6, 12, 8, 16, 12]

theorem plane315GenLeaf0003 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_4 : (2 : Int) ≤ x 4)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0003Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0003Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 21
  · exact hroot.hOcc 33
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (4 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (21 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
