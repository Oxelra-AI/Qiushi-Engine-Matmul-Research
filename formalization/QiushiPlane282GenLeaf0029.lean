import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0029Refs : Fin 26 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 12, .occ 15, .occ 16, .occ 19, .occ 21, .occ 38, .occ 48, .occ 50, .occ 55, .occ 59, .occ 63, .occ 69, .occ 70, .occ 74, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 13, .nonneg 20, .branchLe 12 (0), .branchGe 18 (1), .branchGe 19 (1), .branchLe 0 (2)]

def plane282GenLeaf0029Mult : Fin 26 → Nat := ![5, 7, 1, 2, 3, 4, 3, 3, 4, 1, 1, 1, 4, 2, 1, 5, 3, 3, 3, 11, 1, 2, 5, 10, 6, 7]

theorem plane282GenLeaf0029 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0029Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0029Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 38
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 55
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 74
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (0 : Fin 28) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
