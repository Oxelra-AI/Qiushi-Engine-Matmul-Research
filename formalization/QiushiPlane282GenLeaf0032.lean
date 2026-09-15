import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0032Refs : Fin 28 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 12, .occ 15, .occ 17, .occ 47, .occ 48, .occ 52, .occ 55, .occ 63, .occ 67, .occ 69, .occ 74, .occ 87, .occ 88, .occ 89, .occ 90, .sumGe, .nonneg 9, .nonneg 17, .nonneg 23, .nonneg 24, .branchGe 12 (1), .branchLe 8 (1), .branchLe 2 (1), .branchLe 22 (1), .branchLe 16 (0), .branchGe 19 (1)]

def plane282GenLeaf0032Mult : Fin 28 → Nat := ![24, 16, 3, 20, 19, 14, 14, 2, 1, 11, 7, 19, 2, 4, 4, 1, 3, 28, 4, 1, 23, 13, 30, 19, 18, 9, 14, 19]

theorem plane282GenLeaf0032 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0032Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0032Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (22 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
