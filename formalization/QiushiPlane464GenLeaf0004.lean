import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0004Refs : Fin 51 → RowRef 202 50 := ![.occ 23, .occ 25, .occ 28, .occ 29, .occ 32, .occ 37, .occ 43, .occ 44, .occ 52, .occ 57, .occ 61, .occ 71, .occ 72, .occ 75, .occ 79, .occ 80, .occ 81, .occ 87, .occ 93, .occ 96, .occ 98, .occ 99, .occ 100, .occ 117, .occ 120, .occ 124, .occ 125, .occ 134, .occ 140, .occ 141, .occ 142, .occ 144, .occ 153, .occ 157, .occ 168, .occ 171, .occ 186, .occ 187, .occ 190, .occ 191, .sumGe, .nonneg 0, .nonneg 10, .nonneg 32, .nonneg 33, .nonneg 38, .branchGe 1 (1), .branchLe 49 (0), .branchLe 40 (0), .branchLe 19 (0), .branchLe 18 (0)]

def plane464GenLeaf0004Mult : Fin 51 → Nat := ![8396, 12170, 2618, 2324, 12016, 16362, 5680, 5024, 8690, 17110, 7302, 366, 3134, 16718, 7016, 4968, 12760, 18758, 9894, 2246, 9982, 7340, 5582, 4300, 6948, 6588, 2866, 5998, 10990, 21844, 810, 5890, 1264, 3356, 6874, 8000, 8675, 4293, 1769, 3207, 47066, 62680, 6874, 50364, 5664, 7168, 42690, 47066, 23340, 41004, 38302]

theorem plane464GenLeaf0004 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0004Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0004Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 37
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 52
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (49 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (40 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (18 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
