import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0003Refs : Fin 46 → RowRef 237 50 := ![.occ 8, .occ 9, .occ 10, .occ 24, .occ 27, .occ 28, .occ 46, .occ 55, .occ 58, .occ 74, .occ 75, .occ 78, .occ 81, .occ 85, .occ 91, .occ 96, .occ 101, .occ 102, .occ 121, .occ 122, .occ 123, .occ 154, .occ 167, .occ 168, .occ 176, .occ 177, .occ 178, .occ 182, .occ 192, .occ 193, .occ 198, .occ 205, .occ 207, .sumGe, .nonneg 9, .nonneg 16, .nonneg 17, .nonneg 39, .nonneg 40, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchGe 45 (1), .branchLe 14 (0), .branchLe 37 (0), .branchLe 32 (0)]

def plane427GenLeaf0003Mult : Fin 46 → Nat := ![9, 9, 9, 3, 3, 3, 3, 3, 3, 3, 6, 9, 6, 5, 6, 6, 4, 3, 9, 9, 9, 3, 3, 4, 3, 2, 1, 3, 5, 1, 3, 2, 6, 15, 6, 6, 3, 6, 3, 6, 6, 9, 57, 15, 12, 15]

theorem plane427GenLeaf0003 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0003Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0003Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 46
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 154
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (14 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (37 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (32 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32

end QiushiMatmul
