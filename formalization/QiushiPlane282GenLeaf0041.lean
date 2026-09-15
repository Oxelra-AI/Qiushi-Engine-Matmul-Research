import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0041Refs : Fin 20 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 18, .occ 33, .occ 44, .occ 47, .occ 48, .occ 56, .occ 58, .occ 60, .occ 62, .occ 74, .occ 76, .occ 88, .sumGe, .nonneg 17, .branchGe 12 (1), .branchGe 8 (2), .branchLe 9 (0), .branchLe 4 (1)]

def plane282GenLeaf0041Mult : Fin 20 → Nat := ![2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 6, 4, 4]

theorem plane282GenLeaf0041 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_8 : (2 : Int) ≤ x 8)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0041Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0041Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 18
  · exact hroot.hOcc 33
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 88
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
