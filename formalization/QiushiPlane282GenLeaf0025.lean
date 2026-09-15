import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0025Refs : Fin 26 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 15, .occ 36, .occ 37, .occ 48, .occ 50, .occ 61, .occ 63, .occ 69, .occ 74, .occ 76, .occ 87, .occ 90, .occ 94, .sumGe, .nonneg 3, .nonneg 10, .nonneg 11, .nonneg 13, .nonneg 20, .nonneg 24, .branchLe 12 (0), .branchLe 18 (0), .branchGe 19 (1), .branchGe 14 (1)]

def plane282GenLeaf0025Mult : Fin 26 → Nat := ![2, 8, 3, 1, 6, 9, 1, 2, 1, 3, 2, 1, 4, 4, 6, 12, 2, 3, 8, 3, 9, 11, 9, 9, 16, 8]

theorem plane282GenLeaf0025 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0025Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0025Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 15
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (14 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
