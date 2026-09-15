import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0028Refs : Fin 19 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 11, .occ 19, .occ 27, .occ 47, .occ 52, .occ 54, .occ 74, .occ 76, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 17, .nonneg 24, .branchLe 12 (0), .branchGe 18 (1), .branchGe 11 (1)]

def plane282GenLeaf0028Mult : Fin 19 → Nat := ![2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5]

theorem plane282GenLeaf0028 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0028Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0028Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 11
  · exact hroot.hOcc 19
  · exact hroot.hOcc 27
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
