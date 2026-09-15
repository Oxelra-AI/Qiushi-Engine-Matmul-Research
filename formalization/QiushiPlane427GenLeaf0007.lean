import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0007Refs : Fin 50 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 11, .occ 12, .occ 24, .occ 45, .occ 48, .occ 56, .occ 63, .occ 66, .occ 67, .occ 116, .occ 124, .occ 140, .occ 153, .occ 164, .occ 168, .occ 172, .occ 173, .occ 175, .occ 176, .occ 178, .occ 183, .occ 187, .occ 188, .occ 190, .occ 192, .occ 193, .occ 200, .occ 201, .occ 203, .occ 206, .occ 210, .occ 214, .occ 220, .occ 226, .sumGe, .nonneg 12, .nonneg 13, .nonneg 16, .nonneg 17, .nonneg 27, .nonneg 29, .nonneg 40, .nonneg 46, .nonneg 49, .branchLe 26 (0), .branchLe 15 (0), .branchGe 35 (1), .branchLe 34 (0)]

def plane427GenLeaf0007Mult : Fin 50 → Nat := ![288, 1291, 168, 861, 522, 522, 81, 829, 115, 720, 100, 556, 1009, 231, 194, 378, 144, 55, 60, 134, 241, 1101, 158, 74, 102, 194, 241, 134, 139, 522, 194, 721, 837, 357, 910, 1004, 2410, 115, 267, 915, 268, 168, 747, 2384, 1392, 840, 1379, 1647, 5473, 2216]

theorem plane427GenLeaf0007 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0007Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0007Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 24
  · exact hroot.hOcc 45
  · exact hroot.hOcc 48
  · exact hroot.hOcc 56
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 140
  · exact hroot.hOcc 153
  · exact hroot.hOcc 164
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · exact hroot.hOcc 220
  · exact hroot.hOcc 226
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (34 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
