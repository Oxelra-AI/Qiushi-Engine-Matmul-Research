import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0004Refs : Fin 49 → RowRef 237 50 := ![.occ 7, .occ 15, .occ 27, .occ 29, .occ 32, .occ 44, .occ 56, .occ 65, .occ 72, .occ 76, .occ 80, .occ 81, .occ 96, .occ 101, .occ 117, .occ 122, .occ 123, .occ 152, .occ 153, .occ 156, .occ 170, .occ 181, .occ 182, .occ 187, .occ 194, .occ 195, .occ 210, .occ 214, .occ 223, .occ 224, .occ 226, .occ 231, .sumGe, .nonneg 5, .nonneg 7, .nonneg 13, .nonneg 16, .nonneg 20, .nonneg 24, .nonneg 27, .nonneg 38, .nonneg 41, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchGe 45 (1), .branchLe 14 (0), .branchLe 37 (0), .branchGe 32 (1)]

def plane427GenLeaf0004Mult : Fin 49 → Nat := ![12, 1, 5, 3, 28, 11, 4, 6, 14, 9, 6, 5, 11, 12, 3, 14, 5, 17, 8, 3, 8, 10, 10, 5, 5, 4, 5, 8, 3, 10, 2, 2, 30, 13, 4, 2, 4, 3, 1, 6, 2, 15, 15, 1, 8, 79, 11, 5, 59]

theorem plane427GenLeaf0004 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0004Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0004Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 15
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 44
  · exact hroot.hOcc 56
  · exact hroot.hOcc 65
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 96
  · exact hroot.hOcc 101
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 170
  · exact hroot.hOcc 181
  · exact hroot.hOcc 182
  · exact hroot.hOcc 187
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (14 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (37 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
