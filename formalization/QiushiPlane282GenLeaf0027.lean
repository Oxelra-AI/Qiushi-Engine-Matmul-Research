import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0027Refs : Fin 29 → RowRef 100 28 := ![.occ 3, .occ 4, .occ 9, .occ 19, .occ 21, .occ 37, .occ 47, .occ 49, .occ 50, .occ 54, .occ 56, .occ 60, .occ 63, .occ 64, .occ 69, .occ 74, .occ 84, .occ 87, .occ 90, .sumGe, .nonneg 5, .nonneg 12, .nonneg 13, .nonneg 21, .nonneg 24, .branchGe 4 (2), .branchGe 18 (1), .branchLe 19 (0), .branchLe 11 (0)]

def plane282GenLeaf0027Mult : Fin 29 → Nat := ![2, 14, 4, 17, 18, 8, 23, 1, 4, 10, 1, 2, 6, 5, 2, 5, 2, 11, 12, 25, 1, 2, 27, 1, 26, 22, 56, 5, 3]

theorem plane282GenLeaf0027 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (2 : Int) ≤ x 4)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0027Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0027Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 37
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (21 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (4 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (11 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
