import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0019Refs : Fin 18 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 29, .occ 41, .occ 44, .occ 50, .occ 63, .occ 76, .occ 77, .occ 87, .sumGe, .nonneg 7, .nonneg 11, .nonneg 17, .branchGe 22 (2), .branchLe 8 (1), .branchGe 1 (1), .branchGe 2 (2)]

def plane282GenLeaf0019Mult : Fin 18 → Nat := ![2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2]

theorem plane282GenLeaf0019 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (2 : Int) ≤ x 2)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0019Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0019Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 29
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 50
  · exact hroot.hOcc 63
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 87
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (8 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
