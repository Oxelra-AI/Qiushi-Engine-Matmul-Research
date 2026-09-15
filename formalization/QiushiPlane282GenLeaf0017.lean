import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0017Refs : Fin 18 → RowRef 100 28 := ![.occ 9, .occ 29, .occ 48, .occ 60, .occ 61, .occ 63, .occ 69, .occ 75, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 20, .nonneg 24, .branchLe 18 (0), .branchGe 22 (2), .branchLe 8 (1), .branchGe 26 (1)]

def plane282GenLeaf0017Mult : Fin 18 → Nat := ![2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4]

theorem plane282GenLeaf0017 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0017Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0017Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 29
  · exact hroot.hOcc 48
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (24 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
