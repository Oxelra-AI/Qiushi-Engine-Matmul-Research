import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0008Refs : Fin 23 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 30, .occ 48, .occ 58, .occ 61, .occ 63, .occ 65, .occ 87, .occ 88, .occ 90, .occ 93, .sumGe, .nonneg 11, .nonneg 13, .nonneg 19, .nonneg 20, .nonneg 25, .branchLe 12 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 6 (2), .branchGe 26 (1)]

def plane282GenLeaf0008Mult : Fin 23 → Nat := ![3, 2, 4, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5, 1, 2, 3, 5, 2, 10]

theorem plane282GenLeaf0008 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_6 : (2 : Int) ≤ x 6)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0008Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0008Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 30
  · exact hroot.hOcc 48
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
