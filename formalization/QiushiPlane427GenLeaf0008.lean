import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0008Refs : Fin 51 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 9, .occ 11, .occ 45, .occ 50, .occ 55, .occ 58, .occ 64, .occ 99, .occ 109, .occ 115, .occ 124, .occ 140, .occ 153, .occ 154, .occ 157, .occ 158, .occ 168, .occ 169, .occ 179, .occ 180, .occ 182, .occ 183, .occ 187, .occ 188, .occ 193, .occ 195, .occ 197, .occ 200, .occ 202, .occ 203, .occ 206, .occ 210, .occ 218, .occ 236, .sumGe, .nonneg 7, .nonneg 20, .nonneg 25, .nonneg 29, .nonneg 31, .nonneg 40, .nonneg 41, .nonneg 43, .nonneg 44, .branchLe 26 (0), .branchLe 15 (0), .branchGe 35 (1), .branchGe 34 (1), .branchLe 36 (0)]

def plane427GenLeaf0008Mult : Fin 51 → Nat := ![9051, 44001, 43872, 43912, 8453, 33696, 23121, 2080, 37843, 14095, 6560, 27630, 21758, 22655, 12882, 28928, 12457, 15626, 22576, 4593, 32188, 15568, 7889, 2130, 420, 321, 7279, 27898, 4926, 3641, 22508, 12272, 5610, 5447, 6914, 16931, 83924, 59160, 3399, 36817, 20305, 11852, 17543, 49315, 31136, 20884, 67878, 56026, 121786, 103443, 80283]

theorem plane427GenLeaf0008 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0008Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0008Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 11
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 64
  · exact hroot.hOcc 99
  · exact hroot.hOcc 109
  · exact hroot.hOcc 115
  · exact hroot.hOcc 124
  · exact hroot.hOcc 140
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 182
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 197
  · exact hroot.hOcc 200
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 218
  · exact hroot.hOcc 236
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (34 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
