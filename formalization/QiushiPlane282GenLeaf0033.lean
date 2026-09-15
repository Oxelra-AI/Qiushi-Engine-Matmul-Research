import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0033Refs : Fin 26 → RowRef 100 28 := ![.occ 4, .occ 7, .occ 9, .occ 10, .occ 12, .occ 21, .occ 37, .occ 60, .occ 63, .occ 69, .occ 71, .occ 88, .occ 90, .occ 95, .sumGe, .nonneg 9, .nonneg 10, .nonneg 13, .nonneg 17, .nonneg 24, .nonneg 26, .branchGe 12 (1), .branchLe 8 (1), .branchLe 2 (1), .branchGe 16 (1), .branchLe 1 (0)]

def plane282GenLeaf0033Mult : Fin 26 → Nat := ![3, 2, 4, 1, 4, 1, 1, 6, 4, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4, 6, 3, 2, 7, 2]

theorem plane282GenLeaf0033 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0033Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0033Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 21
  · exact hroot.hOcc 37
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (16 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (1 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
