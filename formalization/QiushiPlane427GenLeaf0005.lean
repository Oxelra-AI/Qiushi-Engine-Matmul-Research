import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0005Refs : Fin 49 → RowRef 237 50 := ![.occ 8, .occ 11, .occ 12, .occ 25, .occ 26, .occ 33, .occ 40, .occ 51, .occ 59, .occ 63, .occ 65, .occ 79, .occ 80, .occ 85, .occ 100, .occ 111, .occ 116, .occ 122, .occ 123, .occ 131, .occ 153, .occ 165, .occ 167, .occ 175, .occ 181, .occ 185, .occ 190, .occ 202, .occ 203, .occ 211, .occ 213, .occ 224, .occ 228, .occ 235, .sumGe, .nonneg 7, .nonneg 12, .nonneg 20, .nonneg 21, .nonneg 24, .nonneg 31, .nonneg 33, .nonneg 38, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchGe 45 (1), .branchLe 14 (0), .branchGe 37 (1)]

def plane427GenLeaf0005Mult : Fin 49 → Nat := ![42, 12, 30, 6, 10, 2, 14, 26, 6, 2, 20, 18, 24, 40, 8, 4, 12, 6, 24, 14, 46, 13, 6, 7, 20, 4, 33, 5, 9, 22, 16, 5, 13, 9, 64, 12, 38, 36, 14, 48, 20, 24, 56, 26, 14, 64, 154, 6, 144]

theorem plane427GenLeaf0005 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0005Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0005Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 33
  · exact hroot.hOcc 40
  · exact hroot.hOcc 51
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 100
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 131
  · exact hroot.hOcc 153
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 181
  · exact hroot.hOcc 185
  · exact hroot.hOcc 190
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 211
  · exact hroot.hOcc 213
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (14 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
