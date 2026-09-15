import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0031Refs : Fin 24 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 13, .occ 19, .occ 21, .occ 23, .occ 47, .occ 52, .occ 54, .occ 60, .occ 63, .occ 69, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 13, .nonneg 24, .nonneg 26, .branchGe 12 (1), .branchLe 8 (1), .branchLe 2 (1), .branchLe 22 (1), .branchLe 19 (0)]

def plane282GenLeaf0031Mult : Fin 24 → Nat := ![8, 7, 7, 2, 3, 5, 2, 1, 1, 7, 1, 6, 1, 1, 1, 9, 2, 3, 1, 7, 7, 7, 6, 7]

theorem plane282GenLeaf0031 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0031Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0031Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (22 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
