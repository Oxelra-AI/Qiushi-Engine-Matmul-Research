import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0034Refs : Fin 23 → RowRef 100 28 := ![.occ 4, .occ 7, .occ 9, .occ 12, .occ 17, .occ 18, .occ 45, .occ 52, .occ 60, .occ 61, .occ 63, .occ 69, .occ 93, .sumGe, .nonneg 13, .nonneg 25, .nonneg 26, .branchGe 12 (1), .branchLe 8 (1), .branchLe 2 (1), .branchLe 22 (1), .branchGe 16 (1), .branchGe 1 (1)]

def plane282GenLeaf0034Mult : Fin 23 → Nat := ![5, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 5, 1, 2, 3, 5, 5, 5, 2, 4, 4]

theorem plane282GenLeaf0034 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0034Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0034Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 45
  · exact hroot.hOcc 52
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 93
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (25 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (22 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
