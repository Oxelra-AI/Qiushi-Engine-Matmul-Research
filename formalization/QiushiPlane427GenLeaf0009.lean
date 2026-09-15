import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0009Refs : Fin 39 → RowRef 237 50 := ![.occ 9, .occ 13, .occ 24, .occ 32, .occ 44, .occ 50, .occ 56, .occ 57, .occ 58, .occ 62, .occ 69, .occ 73, .occ 106, .occ 107, .occ 108, .occ 110, .occ 146, .occ 147, .occ 153, .occ 154, .occ 200, .occ 214, .occ 215, .occ 219, .occ 220, .sumGe, .nonneg 2, .nonneg 13, .nonneg 17, .nonneg 20, .nonneg 24, .nonneg 33, .nonneg 46, .nonneg 49, .branchLe 26 (0), .branchLe 15 (0), .branchGe 35 (1), .branchGe 34 (1), .branchGe 36 (1)]

def plane427GenLeaf0009Mult : Fin 39 → Nat := ![8, 4, 7, 10, 1, 9, 4, 2, 4, 6, 6, 12, 2, 6, 4, 6, 4, 2, 6, 6, 16, 10, 10, 4, 4, 16, 40, 12, 6, 7, 6, 1, 12, 12, 16, 16, 45, 32, 36]

theorem plane427GenLeaf0009 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0009Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0009Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 24
  · exact hroot.hOcc 32
  · exact hroot.hOcc 44
  · exact hroot.hOcc 50
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 200
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (34 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
