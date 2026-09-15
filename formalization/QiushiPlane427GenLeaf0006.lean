import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0006Refs : Fin 47 → RowRef 237 50 := ![.occ 7, .occ 9, .occ 14, .occ 20, .occ 29, .occ 42, .occ 47, .occ 56, .occ 61, .occ 74, .occ 75, .occ 76, .occ 77, .occ 80, .occ 91, .occ 101, .occ 113, .occ 121, .occ 122, .occ 143, .occ 149, .occ 151, .occ 163, .occ 165, .occ 174, .occ 179, .occ 180, .occ 181, .occ 198, .occ 199, .occ 203, .occ 227, .occ 229, .occ 231, .sumGe, .nonneg 4, .nonneg 21, .nonneg 24, .nonneg 28, .nonneg 29, .nonneg 37, .nonneg 46, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchGe 45 (1), .branchGe 14 (1)]

def plane427GenLeaf0006Mult : Fin 47 → Nat := ![9, 14, 5, 6, 3, 2, 4, 4, 1, 11, 3, 1, 4, 1, 2, 5, 2, 3, 5, 7, 2, 10, 9, 10, 7, 7, 2, 4, 4, 13, 4, 5, 5, 11, 27, 2, 31, 7, 2, 16, 4, 21, 6, 23, 9, 58, 63]

theorem plane427GenLeaf0006 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0006Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0006Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 14
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 42
  · exact hroot.hOcc 47
  · exact hroot.hOcc 56
  · exact hroot.hOcc 61
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 91
  · exact hroot.hOcc 101
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 143
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 174
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 203
  · exact hroot.hOcc 227
  · exact hroot.hOcc 229
  · exact hroot.hOcc 231
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
