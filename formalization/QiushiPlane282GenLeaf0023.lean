import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0023Refs : Fin 27 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 15, .occ 16, .occ 20, .occ 42, .occ 48, .occ 50, .occ 57, .occ 58, .occ 63, .occ 69, .occ 74, .occ 76, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 10, .nonneg 11, .nonneg 24, .branchLe 12 (0), .branchGe 4 (1), .branchLe 18 (0), .branchGe 19 (1), .branchLe 14 (0), .branchLe 0 (2)]

def plane282GenLeaf0023Mult : Fin 27 → Nat := ![23, 20, 13, 7, 12, 3, 12, 1, 2, 3, 9, 10, 9, 5, 13, 11, 13, 36, 3, 5, 5, 12, 1, 18, 14, 2, 19]

theorem plane282GenLeaf0023 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0023Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0023Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 20
  · exact hroot.hOcc 42
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (4 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (14 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (0 : Fin 28) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
