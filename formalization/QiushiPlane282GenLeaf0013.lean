import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0013Refs : Fin 20 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 26, .occ 48, .occ 56, .occ 60, .occ 61, .occ 69, .occ 76, .occ 77, .occ 87, .occ 90, .sumGe, .nonneg 11, .nonneg 26, .branchLe 18 (0), .branchLe 8 (1), .branchGe 0 (3), .branchLe 2 (1), .branchLe 6 (1)]

def plane282GenLeaf0013Mult : Fin 20 → Nat := ![3, 3, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3]

theorem plane282GenLeaf0013 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0013Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0013Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 26
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (0 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (6 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
