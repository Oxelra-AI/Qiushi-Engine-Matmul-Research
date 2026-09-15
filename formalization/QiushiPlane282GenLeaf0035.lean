import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0035Refs : Fin 26 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 15, .occ 17, .occ 41, .occ 47, .occ 48, .occ 60, .occ 63, .occ 68, .occ 69, .occ 75, .occ 82, .occ 87, .occ 88, .sumGe, .nonneg 1, .nonneg 7, .nonneg 9, .nonneg 11, .nonneg 17, .nonneg 23, .branchGe 12 (1), .branchLe 8 (1), .branchLe 2 (1), .branchGe 22 (2)]

def plane282GenLeaf0035Mult : Fin 26 → Nat := ![8, 10, 4, 4, 6, 3, 3, 4, 7, 1, 8, 2, 1, 3, 1, 11, 2, 2, 4, 2, 2, 10, 16, 10, 4, 10]

theorem plane282GenLeaf0035 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0035Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0035Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (7 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (9 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
