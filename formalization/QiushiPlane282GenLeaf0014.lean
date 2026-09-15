import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0014Refs : Fin 19 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 62, .occ 63, .occ 66, .occ 76, .occ 77, .occ 85, .occ 87, .occ 88, .occ 91, .occ 99, .sumGe, .nonneg 11, .nonneg 17, .branchLe 12 (0), .branchLe 19 (0), .branchGe 22 (2), .branchGe 6 (2)]

def plane282GenLeaf0014Mult : Fin 19 → Nat := ![2, 4, 4, 7, 1, 4, 4, 1, 7, 7, 1, 2, 11, 7, 7, 4, 4, 13, 13]

theorem plane282GenLeaf0014 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_6 : (2 : Int) ≤ x 6)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (1 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0014Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0014Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 99
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
