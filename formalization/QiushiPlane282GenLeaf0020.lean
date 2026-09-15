import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0020Refs : Fin 23 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 44, .occ 47, .occ 48, .occ 56, .occ 58, .occ 60, .occ 62, .occ 63, .occ 74, .occ 76, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 11, .nonneg 17, .nonneg 26, .branchLe 4 (1), .branchGe 22 (2), .branchGe 8 (2), .branchLe 9 (0)]

def plane282GenLeaf0020Mult : Fin 23 → Nat := ![4, 4, 3, 1, 2, 2, 3, 2, 3, 2, 5, 3, 1, 2, 1, 8, 2, 6, 2, 6, 2, 8, 6]

theorem plane282GenLeaf0020 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_8 : (2 : Int) ≤ x 8)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0020Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0020Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
